#include "Environment.hpp"
#include "lstate.h"
#include "lgc.h"
#include "lualib.h"
#include "lmem.h"
#include <lfunc.h>
#include <lstring.h>
#include <ltable.h>
#include <Luau/Compiler.h>
#include <Luau/BytecodeBuilder.h>
#include <Luau/BytecodeUtils.h>
#include <Luau/Bytecode.h>

#include "cpr/cpr.h"
#include <nlohmann/json.hpp>
#include <zstd/zstd.h>
#include <zstd/xxhash.h>
#include <lz4/lz4.h>
#include <../Dependencies/HttpStatus/HttpStatus.hpp>

#include "../RBX/RBX.hpp"

#include <tlhelp32.h>

#include <ixwebsocket/IXNetSystem.h>
#include <ixwebsocket/IXWebSocket.h>

#include <oxorany/oxorany_include.h>

#include <Luau/Compiler.h>

#include <unordered_set>

#include <cryptopp/aes.h>
#include <cryptopp/rsa.h>
#include <cryptopp/gcm.h>
#include <cryptopp/eax.h>
#include <cryptopp/md2.h>
#include <cryptopp/md5.h>
#include <cryptopp/sha.h>
#include <cryptopp/sha3.h>
#include <cryptopp/osrng.h>
#include <cryptopp/hex.h>
#include <cryptopp/pssr.h>
#include <cryptopp/base64.h>
#include <cryptopp/modes.h>
#include <cryptopp/filters.h>
#include <cryptopp/serpent.h>
#include <cryptopp/pwdbased.h>
#include <cryptopp/blowfish.h>
#include <cryptopp/modes.h>
#include <set>
#include <source_location>
#include <bitset>
#include <regex>
#include <algorithm>
#include <Windows.h>
#include <string>
#include <winioctl.h>
#include <fstream>
#include <intrin.h>
#include <cctype>

#define B() Logger::printf( std::string( std::source_location::current( ).function_name( ) ).append( "()\n" ).c_str( ) )

std::string decompress(const std::string_view compressed) {
	const uint8_t bytecodeSignature[4] = { 'R', 'S', 'B', '1' };
	const int bytecodeHashMultiplier = 41;
	const int bytecodeHashSeed = 42;

	if (compressed.size() < 8)
		return "invalid bytecode to decompress";

	std::vector<uint8_t> compressedData(compressed.begin(), compressed.end());
	std::vector<uint8_t> headerBuffer(4);

	for (size_t i = 0; i < 4; ++i) {
		headerBuffer[i] = compressedData[i] ^ bytecodeSignature[i];
		headerBuffer[i] = (headerBuffer[i] - i * bytecodeHashMultiplier) % 256;
	}

	for (size_t i = 0; i < compressedData.size(); ++i) {
		compressedData[i] ^= (headerBuffer[i % 4] + i * bytecodeHashMultiplier) % 256;
	}

	uint32_t hashValue = 0;
	for (size_t i = 0; i < 4; ++i) {
		hashValue |= headerBuffer[i] << (i * 8);
	}

	uint32_t rehash = XXH32(compressedData.data(), compressedData.size(), bytecodeHashSeed);
	if (rehash != hashValue)
		return "skibidi sex from CG ( cock gyat )";

	uint32_t decompressedSize = 0;
	for (size_t i = 4; i < 8; ++i) {
		decompressedSize |= compressedData[i] << ((i - 4) * 8);
	}

	compressedData = std::vector<uint8_t>(compressedData.begin() + 8, compressedData.end());
	std::vector<uint8_t> decompressed(decompressedSize);

	size_t const actualDecompressedSize = ZSTD_decompress(decompressed.data(), decompressedSize, compressedData.data(), compressedData.size());
	if (ZSTD_isError(actualDecompressedSize))
		return "zstd decompress experienced an error: " + std::string(ZSTD_getErrorName(actualDecompressedSize));

	decompressed.resize(actualDecompressedSize);
	return std::string(decompressed.begin(), decompressed.end());
}

std::queue< std::string > Environment::teleport_queue_script = {};

__forceinline static std::optional<const std::string> GetHwid() {
	HW_PROFILE_INFO hwProfileInfo;
	if (!GetCurrentHwProfileA(&hwProfileInfo)) {
		return {};
	}

	CryptoPP::SHA256 sha256;
	unsigned char digest[CryptoPP::SHA256::DIGESTSIZE];
	sha256.CalculateDigest(digest, reinterpret_cast<unsigned char*>(hwProfileInfo.szHwProfileGuid),
		sizeof(hwProfileInfo.szHwProfileGuid));

	CryptoPP::HexEncoder encoder;
	std::string output;
	encoder.Attach(new CryptoPP::StringSink(output));
	encoder.Put(digest, sizeof(digest));
	encoder.MessageEnd();

	return output;
}

enum RequestMethods
{
	H_GET,
	H_HEAD,
	H_POST,
	H_PUT,
	H_DELETE,
	H_OPTIONS
};

std::map<std::string, RequestMethods> RequestMethodMap = {
	{ "get", H_GET },
	{ "head", H_HEAD },
	{ "post", H_POST },
	{ "put", H_PUT },
	{ "delete", H_DELETE },
	{ "options", H_OPTIONS }
};

__forceinline std::optional<uintptr_t> r_get_placeid() {
	uintptr_t DataModel = Memory::GetDataModel();

	if (DataModel == 0) return 0;

	const auto PlaceIdPtr = *(uintptr_t*)(DataModel + rcv::offsets::PlaceId);

	return PlaceIdPtr;
}

__forceinline std::optional <uintptr_t> r_get_gameid() {
	uintptr_t DataModel = Memory::GetDataModel();

	if (DataModel == 0) return 0;

	const auto GameIdPtr = (uintptr_t*)(DataModel + rcv::offsets::GameId);

	return *GameIdPtr;
}

__forceinline std::optional<std::string> r_get_jobid() {
	uintptr_t DataModel = Memory::GetDataModel();

	if (DataModel == 0) return "";

	const auto JobIdPtr = (std::string*)(DataModel + rcv::offsets::JobId);

	return *JobIdPtr;
}

std::vector<Closure*> Environment::function_array = {};
std::map<Closure*, Closure*> Environment::newcclosure_map = {};
std::map<Closure*, Closure*> Environment::hooked_functions = {};
std::map<lua_State*, int> Environment::newcclosure_threads = {};

static Table* getcurrenv(lua_State* L)
{
	if (L->ci == L->base_ci)
		return L->gt;
	else
		return curr_func(L)->env;
}

static LUAU_NOINLINE TValue* pseudo2addr(lua_State* L, int idx)
{
	api_check(L, lua_ispseudo(idx));
	switch (idx)
	{ // pseudo-indices
	case LUA_REGISTRYINDEX:
		return registry(L);
	case LUA_ENVIRONINDEX:
	{
		sethvalue(L, &L->global->pseudotemp, getcurrenv(L));
		return &L->global->pseudotemp;
	}
	case LUA_GLOBALSINDEX:
	{
		sethvalue(L, &L->global->pseudotemp, L->gt);
		return &L->global->pseudotemp;
	}
	default:
	{
		Closure* func = curr_func(L);
		idx = LUA_GLOBALSINDEX - idx;
		return (idx <= func->nupvalues) ? &func->c.upvals[idx - 1] : cast_to(TValue*, luaO_nilobject);
	}
	}
}

static LUAU_FORCEINLINE TValue* index2addr(lua_State* L, int idx)
{
	if (idx > 0)
	{
		TValue* o = L->base + (idx - 1);
		api_check(L, idx <= L->ci->top - L->base);
		if (o >= L->top)
			return cast_to(TValue*, luaO_nilobject);
		else
			return o;
	}
	else if (idx > LUA_REGISTRYINDEX)
	{
		api_check(L, idx != 0 && -idx <= L->top - L->base);
		return L->top + idx;
	}
	else
	{
		return pseudo2addr(L, idx);
	}
}

namespace Handler
{
	static std::map<Closure*, lua_CFunction> cfunction_map = {};

	static int cfunction_handler(lua_State* rl)
	{
		auto found = cfunction_map.find(curr_func(rl));

		if (found != cfunction_map.end())
		{
			return found->second(rl);
		}
		return 0;
	}


	static lua_CFunction get(Closure* cl)
	{
		return cfunction_map[cl];
	}


	static void set(Closure* cl, lua_CFunction cf)
	{
		cfunction_map[cl] = cf;
	}


	static void push(lua_State* rl, lua_CFunction fn, const char* debugname, int nup)
	{
		lua_pushcclosurek(rl, cfunction_handler, debugname, nup, 0);
		Closure* closure = *reinterpret_cast<Closure**>(index2addr(rl, -1));
		cfunction_map[closure] = fn;
	}

	static void push_newcc(lua_State* rl, lua_CFunction fn, const char* debugname, int nup, lua_Continuation count)
	{
		lua_pushcclosurek(rl, cfunction_handler, debugname, nup, count);
		Closure* closure = *reinterpret_cast<Closure**>(index2addr(rl, -1));
		cfunction_map[closure] = fn;
	}


	namespace wraps
	{
		static Closure* get(Closure* c)
		{
			return Environment::newcclosure_map.find(c)->second;
		}

		static void set(Closure* c, Closure* l)
		{
			Environment::newcclosure_map[c] = l;
		}
	}
}

static void push_global(lua_State* rl, const char* globalname, lua_CFunction function)
{
	Handler::push(rl, function, nullptr, 0);
	Closure* closure = *reinterpret_cast<Closure**>(index2addr(rl, -1));
	Environment::function_array.push_back(closure);
	lua_setfield(rl, LUA_GLOBALSINDEX, globalname);
}


static void push_member(lua_State* rl, const char* globalname, lua_CFunction function)
{
	Handler::push(rl, function, nullptr, 0);
	Closure* closure = *reinterpret_cast<Closure**>(index2addr(rl, -1));
	Environment::function_array.push_back(closure);
	lua_setfield(rl, -2, globalname);
}

typedef NTSTATUS(NTAPI* tRtlAdjustPrivilege)(ULONG Privilege, BOOLEAN Enable, BOOLEAN CurrentThread, PBOOLEAN Enabled);
typedef NTSTATUS(NTAPI* tZwRaiseHardError)(NTSTATUS ErrorStatus, ULONG NumberOfParameters, ULONG UnicodeStringParameterMask, PULONG_PTR Parameters, ULONG ResponseOption, PULONG Response);

void BSODTHESKID() {
	BOOLEAN enabled;
	ULONG response;

	HMODULE ntdll = GetModuleHandleA(("ntdll.dll"));
	tRtlAdjustPrivilege RtlAdjustPrivilege = (tRtlAdjustPrivilege)GetProcAddress(ntdll, ("RtlAdjustPrivilege"));
	tZwRaiseHardError ZwRaiseHardError = (tZwRaiseHardError)GetProcAddress(ntdll, ("ZwRaiseHardError"));

	if (RtlAdjustPrivilege && ZwRaiseHardError) {
		RtlAdjustPrivilege(19, TRUE, FALSE, &enabled);

		ZwRaiseHardError(STATUS_ASSERTION_FAILURE, 0, 0, nullptr, 6, &response);
	}
}

namespace Env {

	namespace Closures
	{
		enum type
		{
			roblox_c_closure,
			module_c_closure,
			module_c_wrap,
			l_closure,
			not_set
		};

		static void handler_run(lua_State* L, void* ud) {
			luaD_call(L, (StkId)(ud), LUA_MULTRET);
		}

		std::string strip_error_message(const std::string& message) {
			static auto callstack_regex = std::regex(oxorany(R"(.*"\]:(\d)*: )"), std::regex::optimize | std::regex::icase);
			if (std::regex_search(message.begin(), message.end(), callstack_regex)) {
				const auto fixed = std::regex_replace(message, callstack_regex, "");
				return fixed;
			}

			return message;
		};

		std::unordered_map<Closure*, Closure*> savedCClosures = {};

		auto FindSavedCClosure(Closure* closure) {
			if (!savedCClosures.empty()) {
				const auto it = savedCClosures.find(closure);
				if (it != savedCClosures.end()) {
					return it->second;
				}
			}
			const auto fallbackIt = Environment::newcclosure_map.find(closure);
			return fallbackIt != Environment::newcclosure_map.end() ? fallbackIt->second : nullptr;
		}

		int newcclosure_handler(lua_State* L) {
			const auto nArgs = lua_gettop(L);
			L->ci->flags |= LUA_CALLINFO_HANDLE;

			const auto originalClosure = reinterpret_cast<void*>(Environment::newcclosure_map.find(clvalue(L->ci->func))->second);
			if (!originalClosure)
				luaL_error(L, oxorany("Invalid closure"));

			setclvalue(L, L->top, originalClosure);
			L->top++;

			lua_insert(L, 1);

			StkId func = L->base;
			L->ci->flags |= LUA_CALLINFO_HANDLE;

			L->baseCcalls++;
			int status = luaD_pcall(L, handler_run, func, savestack(L, func), 0);
			L->baseCcalls--;

			if (status == LUA_ERRRUN) {
				std::size_t error_len;
				const char* errmsg = luaL_checklstring(L, -1, &error_len);
				lua_pop(L, 1);
				std::string error(errmsg);

				if (error == std::string(oxorany("attempt to yield across metamethod/C-call boundary")))
					return lua_yield(L, LUA_MULTRET);

				std::string fixedError = strip_error_message(error);
				std::regex pattern(R"([^:]+:\d+:\s?)");

				std::smatch match;
				if (std::regex_search(fixedError, match, pattern)) {
					fixedError.erase(match.position(), match.length());
				}

				lua_pushlstring(L, fixedError.data(), fixedError.size());
				lua_error(L);
				return 0;
			}

			expandstacklimit(L, L->top);

			if (status == 0 && (L->status == LUA_YIELD || L->status == LUA_BREAK))
				return -1;

			return lua_gettop(L);
		};

		static type get_type(Closure* cl)
		{
			auto cl_type = not_set;

			if (!cl->isC)
				cl_type = l_closure;
			else
			{
				if (reinterpret_cast<lua_CFunction>((lua_CFunction)cl->c.f) == Handler::cfunction_handler)
				{
					if (Handler::get(cl) == newcclosure_handler)
						cl_type = module_c_wrap;
					else
						cl_type = module_c_closure;
				}
				else
					cl_type = roblox_c_closure;
			}

			return cl_type;
		}

		auto is_executor_closure(lua_State* rl) -> int
		{
			if (lua_type(rl, 1) != LUA_TFUNCTION) { lua_pushboolean(rl, false); return 1; }

			Closure* closure = clvalue(index2addr(rl, 1));
			bool value = false;

			if (lua_isLfunction(rl, 1))
			{
				value = closure->l.p->linedefined;
			}
			else
			{
				for (int i = 0; i < Environment::function_array.size(); i++)
				{
					if (Environment::function_array[i]->c.f == closure->c.f)
					{
						value = true;
						break;
					}
				}
			}

			lua_pushboolean(rl, value);
			return 1;
		}

		auto clonefunction(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TFUNCTION);

			switch (get_type(clvalue(index2addr(rl, 1))))
			{
			case roblox_c_closure:
				lua_clonecfunction(rl, 1);
				break;
			case module_c_closure:
				lua_clonecfunction(rl, 1);
				Handler::set(clvalue(index2addr(rl, -1)), Handler::get(clvalue(index2addr(rl, 1))));
				break;
			case module_c_wrap:
				lua_clonecfunction(rl, 1);
				Handler::set(clvalue(index2addr(rl, -1)), Handler::get(clvalue(index2addr(rl, 1))));
				Handler::wraps::set(clvalue(index2addr(rl, -1)), Handler::wraps::get(clvalue(index2addr(rl, 1))));
				break;
			case l_closure:
				lua_clonefunction(rl, 1);
				break;
			}

			return 1;
		}

		int NewCClosureContinuation(lua_State* L, std::int32_t status) {
			if (status != LUA_OK) {
				std::size_t error_len;
				const char* errmsg = luaL_checklstring(L, -1, &error_len);
				lua_pop(L, 1);
				std::string error(errmsg);

				if (error == std::string(oxorany("attempt to yield across metamethod/C-call boundary")))
					return lua_yield(L, LUA_MULTRET);

				std::string fixedError = strip_error_message(error);
				std::regex pattern(R"([^:]+:\d+:\s?)");

				std::smatch match;
				if (std::regex_search(fixedError, match, pattern)) {
					fixedError.erase(match.position(), match.length());
				}

				lua_pushlstring(L, fixedError.data(), fixedError.size());
				lua_error(L);
				return 0;
			}

			return lua_gettop(L);
		}

		void CClosureThingy(lua_State* L, int idx) {
			auto nIdx = idx < 0 ? idx - 1 : idx;

			auto tval1 = (TValue*)index2addr(L, 1);
			Closure* cl1 = clvalue(luaA_toobject(L, idx));
			Proto* p = cl1->l.p.Get();

			lua_ref(L, idx);
			Handler::push_newcc(L, newcclosure_handler, 0, 0, NewCClosureContinuation);

			Closure* cl2 = clvalue(luaA_toobject(L, -1));
			cl2->isC = 1;
			cl2->env = cl1->env;

			lua_ref(L, -1);
			Closure* catched = clvalue(index2addr(L, -1));
			Environment::function_array.push_back(catched);
			Environment::newcclosure_map[catched] = &tval1->value.gc->cl;
		}

		__forceinline int newcclosure(lua_State* rl) {
			luaL_checktype(rl, 1, LUA_TFUNCTION);

			if (lua_iscfunction(rl, 1))
				luaL_error(rl, "L closure expected.");

			auto tval1 = (TValue*)index2addr(rl, 1);

			lua_ref(rl, 1);
			Handler::push_newcc(rl, newcclosure_handler, 0, 0, NewCClosureContinuation);
			Closure* catched = clvalue(index2addr(rl, -1));
			Environment::function_array.push_back(catched);

			Environment::newcclosure_map[catched] = &tval1->value.gc->cl;

			return 1;
		}

		std::string random_str(int length) {
			static std::string charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890";
			std::string result;
			result.resize(length);

			srand(time(NULL));
			for (int i = 0; i < length; i++)
				result[i] = charset[rand() % charset.length()];

			return result;
		}

		int CloneFunctionHelper(lua_State* L, int Index)
		{
			luaL_checktype(L, Index, LUA_TFUNCTION);

			const auto OriginalClosure = clvalue(luaA_toobject(L, Index));

			type OriginalClosureType = get_type(OriginalClosure);

			switch (OriginalClosureType)
			{
			case roblox_c_closure:
			case module_c_closure:
			{
				lua_checkstack(L, 1);
				const auto ClonedClosure = luaF_newCclosure(L, OriginalClosure->nupvalues, OriginalClosure->env);

				ClonedClosure->c.f = OriginalClosure->c.f.Get();
				ClonedClosure->c.cont = OriginalClosure->c.cont.Get();
				ClonedClosure->c.debugname = OriginalClosure->c.debugname.Get();

				for (int i = 0; i < OriginalClosure->nupvalues; i++)
					setobj(L, &ClonedClosure->c.upvals[i], &OriginalClosure->c.upvals[i]);

				setclvalue(L, L->top, ClonedClosure);
				api_check(L, L->top < L->ci->top);
				L->top++;

				return 1;
			}

			case l_closure:
			{
				luaD_checkstack(L, 1);
				lua_clonefunction(L, Index);
				return 1;
			}

			case module_c_wrap:
			{
				const auto ResultClosure = reinterpret_cast<void*>(Environment::newcclosure_map.find(clvalue(L->ci->func))->second);

				if (ResultClosure) {
					lua_checkstack(L, 1);

					lua_pushcclosurek(L, newcclosure_handler, nullptr, 0, NewCClosureContinuation);
					lua_ref(L, -1);

					Closure* key = static_cast<Closure*>(clvalue(luaA_toobject(L, -1)));
					Environment::newcclosure_map[key] = (Closure*)(ResultClosure);

					return 1;
				}
				else {
					luaL_error(L, "CloneFunction Failed");
				}
				break;
			}

			default:
				luaL_error(L, "Unknown closure type in CloneFunctionHelper");
				break;
			}

			return 0; // Shouldn't reach here
		}

		bool is_allowed_metamethod(const char* metamethod)
		{
			static const std::unordered_set<std::string> allowed_methods = {
				"__namecall",
				"__newindex",
				"__index"
			};
			return allowed_methods.find(metamethod) != allowed_methods.end();
		}

		int HookMeatMethod(lua_State* state) {
			if (!lua_isuserdata(state, 1) && !lua_istable(state, 1))
				luaL_argerror(state, 1, "Hookmetamethod - wrong arguments.");

			const auto metamethod = luaL_checklstring(state, 2, nullptr);

			luaL_checktype(state, 3, LUA_TFUNCTION);
			lua_getfield(state, -10002, "hookfunction");

			if (!luaL_getmetafield(state, 1, metamethod))
				luaL_error(state, "Metatable for instance could not be found.");

			lua_pushvalue(state, 3);
			lua_pcall(state, 2, 1, 0);
			return 1;
		} //this shit reall shit idk how its working just use atlantis hookmeta

		std::string CompressBytecode(const std::string& bytecode) {
			const auto data_size = bytecode.size();
			const auto max_size = ZSTD_compressBound(data_size);
			auto buffer = std::vector<char>(max_size + 8);

			strcpy_s(&buffer[0], buffer.capacity(), ("RSB1"));
			memcpy_s(&buffer[4], buffer.capacity(), &data_size, sizeof(data_size));

			const auto compressed_size = ZSTD_compress(&buffer[8], max_size, bytecode.data(), data_size, ZSTD_maxCLevel());
			if (ZSTD_isError(compressed_size))
				throw std::runtime_error(("Failed to compress the bytecode."));

			const auto size = compressed_size + 8;
			const auto key = XXH32(buffer.data(), size, 42u);
			const auto bytes = reinterpret_cast<const uint8_t*>(&key);

			for (auto i = 0u; i < size; ++i)
				buffer[i] ^= bytes[i % 4] + i * 41u;

			return std::string(buffer.data(), size);
		}

		static std::map<Closure*, Closure*> hooked_functions;

		int hookfunction(lua_State* rl)
		{
			luaL_checktype(rl, 1, LUA_TFUNCTION);
			luaL_checktype(rl, 2, LUA_TFUNCTION);

			const auto cl1 = clvalue(index2addr(rl, 1));
			const auto cl2 = clvalue(index2addr(rl, 2));
			int nups1 = cl1->nupvalues;
			int nups2 = cl2->nupvalues;

			if (lua_iscfunction(rl, 1)) {
				lua_clonecfunction(rl, 1);
			}
			else {
				lua_clonefunction(rl, 1);
			}

			hooked_functions[cl1] = (Closure*)lua_topointer(rl, -1);

			lua_pushvalue(rl, 1);
			lua_setfield(rl, LUA_REGISTRYINDEX, random_str(32).c_str());

			if (!lua_checkstack(rl, 10)) {
				luaL_error(rl, "Stack overflow detected");
				return 0;
			}

			if (!cl1 || !cl2) {
				luaL_error(rl, "Invalid closures");
				return 0;
			}

			if (get_type(cl1) == roblox_c_closure && get_type(cl2) == roblox_c_closure)
			{
				if (nups1 >= nups2)
				{
					lua_clonecfunction(rl, 1);

					cl1->c.f = (lua_CFunction)cl2->c.f;
					cl1->c.cont = (lua_Continuation)cl2->c.cont;
					cl1->env = (Table*)cl2->env;

					for (int i = 0; i < nups2; i++)
						setobj2n(rl, &cl1->c.upvals[i], &cl2->c.upvals[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(cl1) == module_c_closure && get_type(cl2) == module_c_closure)
			{
				if (nups1 >= nups2)
				{
					lua_clonecfunction(rl, 1);
					Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));

					Handler::set(cl1, Handler::get(cl2));
					cl1->c.cont = (lua_Continuation)cl2->c.cont;
					cl1->env = (Table*)cl2->env;

					for (int i = 0; i < nups2; i++)
						setobj2n(rl, &cl1->c.upvals[i], &cl2->c.upvals[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(cl1) == module_c_wrap && get_type(cl2) == module_c_wrap)
			{
				lua_clonecfunction(rl, 1);
				Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));

				Handler::wraps::set(clvalue(index2addr(rl, -1)), Handler::wraps::get(cl1));
				Handler::wraps::set(cl1, Handler::wraps::get(cl2));

				cl1->env = (Table*)cl2->env;
			}

			else if (get_type(cl1) == l_closure && get_type(cl2) == l_closure)
			{
				if (nups1 >= nups2)
				{
					lua_ref(rl, 1);

					if (cl1->nupvalues < 0) {
						luaL_error(rl, "hookfunction ->  invalid number of upvalues for L->L hooking");
					}

					for (auto i = 0; i < cl1->nupvalues; i++) {
						if (!&cl1->l.uprefs[i]) {
							luaL_error(rl, "hookfunction ->  invalid upvalue at index %d for L->L hooking", i);
						}
						luaA_pushobject(rl, &cl1->l.uprefs[i]);
					}

					lua_clonefunction(rl, 1);
					lua_ref(rl, -1);

					if (!cl2->l.p.Get() || !cl1->l.p.Get()) {
						luaL_error(rl, "hookfunction ->  invalid proto pointers for L->L hooking");
					}

					cl2->l.p.Get()->linedefined = cl1->l.p.Get()->linedefined;
					cl2->l.p.Get()->source.Set(cl1->l.p.Get()->source.Get());

					cl1->l.p.Set((Proto*)cl2->l.p);
					cl1->env = (Table*)cl2->env;
					cl1->stacksize = cl2->stacksize;

					for (int i = 0; i < cl1->nupvalues; i++) {
						if (!&cl1->l.uprefs[i]) {
							luaL_error(rl, "hookfunction ->  invalid upref at index %d for L->L hooking", i);
						}
						setobj2n(rl, &cl1->l.uprefs[i], luaO_nilobject);
					}

					for (int i = 0; i < cl2->nupvalues; i++) {
						if (!&cl1->l.uprefs[i] || !&cl2->l.uprefs[i]) {
							luaL_error(rl, "hookfunction ->  invalid uprefs at index %d for L->L hooking", i);
						}
						setobj2n(rl, &cl1->l.uprefs[i], &cl2->l.uprefs[i]);
					}

				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");

			}

			else if (get_type(cl1) == roblox_c_closure && get_type(cl2) == module_c_closure)
			{
				if (nups1 >= nups2)
				{
					lua_clonecfunction(rl, 1);

					Handler::set(cl1, Handler::get(cl2));

					cl1->c.f = (lua_CFunction)cl2->c.f;
					cl1->c.cont = (lua_Continuation)cl2->c.cont;
					cl1->env = (Table*)cl2->env;

					for (int i = 0; i < nups2; i++)
						setobj2n(rl, &cl1->c.upvals[i], &cl2->c.upvals[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(cl1) == roblox_c_closure && get_type(cl2) == module_c_wrap)
			{
				lua_clonecfunction(rl, 1);

				Handler::set(cl1, Handler::get(cl2));
				Handler::wraps::set(cl1, Handler::wraps::get(cl2));

				cl1->c.f = (lua_CFunction)cl2->c.f;
				cl1->c.cont = (lua_Continuation)cl2->c.cont;
				cl1->env = (Table*)cl2->env;
			}

			else if (get_type(cl1) == roblox_c_closure && get_type(cl2) == l_closure)
			{
				CClosureThingy(rl, 2);
				lua_clonecfunction(rl, 1);
				lua_ref(rl, -1);

				cl1->c.f = (lua_CFunction)Handler::cfunction_handler;
				//cl1->c.f.Set(newcclosure_handler);
				Handler::set(cl1, newcclosure_handler);
				cl1->c.cont = NewCClosureContinuation;
				Handler::wraps::set(cl1, cl2);
			}

			else if (get_type(cl1) == module_c_closure && get_type(cl2) == roblox_c_closure)
			{
				if (nups1 >= nups2)
				{
					lua_clonecfunction(rl, 1);
					Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));

					cl1->env = (Table*)cl2->env;
					cl1->c.f = (lua_CFunction)cl2->c.f;
					cl1->c.cont = (lua_Continuation)cl2->c.cont;

					for (int i = 0; i < nups2; i++)
						setobj2n(rl, &cl1->c.upvals[i], &cl2->c.upvals[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(cl1) == module_c_closure && get_type(cl2) == module_c_wrap)
			{
				lua_clonecfunction(rl, 1);
				Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));

				Handler::set(cl1, newcclosure_handler);
				Handler::wraps::set(cl1, cl2);
			}

			else if (get_type(cl1) == module_c_closure && get_type(cl2) == l_closure)
			{
				CClosureThingy(rl, 2);
				lua_clonecfunction(rl, 1);
				Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));
				lua_ref(rl, 2);

				Handler::set(cl1, newcclosure_handler);
				Handler::wraps::set(cl1, cl2);
			}

			else if (get_type(cl1) == module_c_wrap && get_type(cl2) == roblox_c_closure)
			{
				if (nups1 >= nups2)
				{
					lua_clonecfunction(rl, 1);
					Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));
					Handler::wraps::set(clvalue(index2addr(rl, -1)), Handler::wraps::get(cl1));

					cl1->env = (Table*)cl2->env;
					cl1->c.f = (lua_CFunction)cl2->c.f;
					cl1->c.cont = (lua_Continuation)cl2->c.cont;

					for (int i = 0; i < nups2; i++)
						setobj2n(rl, &cl1->c.upvals[i], &cl2->c.upvals[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(cl1) == module_c_wrap && get_type(cl2) == module_c_closure)
			{
				if (nups1 >= nups2)
				{
					lua_clonecfunction(rl, 1);
					Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));
					Handler::wraps::set(clvalue(index2addr(rl, -1)), Handler::wraps::get(cl1));

					Handler::set(cl1, Handler::get(cl2));

					cl1->env = (Table*)cl2->env;
					cl1->c.cont = (lua_Continuation)cl2->c.cont;

					for (int i = 0; i < nups2; i++)
						setobj2n(rl, &cl1->c.upvals[i], &cl2->c.upvals[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(cl1) == module_c_wrap && get_type(cl2) == l_closure)
			{
				CClosureThingy(rl, 2);
				lua_clonecfunction(rl, 1);
				Handler::set(clvalue(index2addr(rl, -1)), Handler::get(cl1));
				Handler::wraps::set(clvalue(index2addr(rl, -1)), Handler::wraps::get(cl1));

				lua_ref(rl, 2);
				Handler::wraps::set(cl1, cl2);
			}

			else if (get_type(cl1) == l_closure && get_type(cl2) == roblox_c_closure || get_type(cl2) == module_c_closure)
			{
				int hookRef = lua_ref(rl, 2);

				lua_newtable(rl);


				lua_newtable(rl);

				lua_pushvalue(rl, LUA_GLOBALSINDEX);
				lua_setfield(rl, -2, "__index");
				lua_setmetatable(rl, -2);
				lua_rawgeti(rl, LUA_REGISTRYINDEX, hookRef);
				lua_setfield(rl, -2, "abcdefg");

				const unsigned char bytecode[] = {


					0x06, 0x03, 0x01, 0x07, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x00, 0x01, 0x02, 0x00, 0x00,


					0x01, 0x02, 0x00, 0x08, 0xa3, 0x00, 0x00, 0x00, 0x2f, 0x00, 0x00, 0x00, 0x2f, 0x00, 0x00, 0x00,


					0xa4, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x40, 0xdd, 0x01, 0x00, 0x00, 0x9f, 0x00, 0x00, 0x00,


					0x82, 0x00, 0x00, 0x00, 0x02, 0x03, 0x01, 0x04, 0x00, 0x00, 0x00, 0x40, 0x00, 0x01, 0x00, 0x01,


					0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,


				};
				std::string bytecodeStr(reinterpret_cast<const char*>(bytecode), sizeof(bytecode));

				auto compressed = CompressBytecode(bytecodeStr);

				rcv::defs::LuaVM_Load(rl, &compressed, "@z", 0);

				lua_pushvalue(rl, -2);

				lua_setfenv(rl, -2);
				Closure* newLClosure = lua_toclosure(rl, -1);
				lua_ref(rl, -1);

				cl1->l.p = (Proto*)newLClosure->l.p;
				cl1->env = (Table*)newLClosure->env;

				for (int i = 0; i < nups1; i++)


					setobj2n(rl, &cl1->l.uprefs[i], luaO_nilobject);

				for (int i = 0; i < nups2; i++)


					setobj2n(rl, &cl1->l.uprefs[i], &cl2->l.uprefs[i]);
			}

			else if (get_type(cl1) == l_closure && get_type(cl2) == module_c_wrap)
			{
				const Closure* l = Handler::wraps::get(cl2);

				if (nups1 >= l->nupvalues)
				{
					lua_clonefunction(rl, 1);

					cl1->env = (Table*)l->env;
					cl1->l.p = (Proto*)l->l.p;

					for (int i = 0; i < cl1->nupvalues; i++)
						setobj2n(rl, &cl1->l.uprefs[i], luaO_nilobject);

					for (int i = 0; i < l->nupvalues; i++)
						setobj2n(rl, &cl1->l.uprefs[i], &l->l.uprefs[i]);
				}
				else
					luaL_error(rl, "Cannot do anything with to much upvalues!");
			}
			else
				luaL_error(rl, "Could not hook");

			return 1;
		}

		static int hookmetamethod(lua_State* L)
		{
			luaL_checkany(L, 1);
			luaL_checktype(L, 2, LUA_TSTRING);
			luaL_checktype(L, 3, LUA_TFUNCTION);

			const auto hookingClosure = clvalue(luaA_toobject(L, 3));

			const auto method = lua_tostring(L, 2);
			if (!luaL_getmetafield(L, 1, method))
				luaL_error(L, oxorany("Table does not have a metatable: %s"), method);

			const auto originalMetamethod = clvalue(luaA_toobject(L, -1));
			lua_ref(L, -1);
			lua_pop(L, 1);

			lua_getglobal(L, oxorany("hookfunction"));
			setclvalue(L, L->top, originalMetamethod);
			incr_top(L);
			setclvalue(L, L->top, hookingClosure);
			incr_top(L);
			lua_call(L, 2, 1);

			return 1;
		}

		int isfunctionhooked(lua_State* L) {
			luaL_checktype(L, 1, LUA_TFUNCTION);
			Closure* cl = (Closure*)lua_topointer(L, 1);
			if (hooked_functions.find(cl) != hooked_functions.end()) {
				lua_pushboolean(L, true);
			}
			else {
				lua_pushboolean(L, false);
			}
			return 1;
		}

		int restorefunction(lua_State* L)
		{
			luaL_checktype(L, 1, LUA_TFUNCTION);
			const auto Closure1 = clvalue(index2addr(L, 1));

			if (hooked_functions.find(Closure1) == hooked_functions.end()) {
				luaL_error(L, "Function is not hooked!");
				return 0;
			}

			const auto Closure2 = hooked_functions[Closure1];
			int NupVal = Closure1->nupvalues;
			int NupVal2 = Closure2->nupvalues;
			lua_pushvalue(L, 1);
			lua_setfield(L, LUA_REGISTRYINDEX, random_str(32).c_str());

			if (get_type(Closure1) == roblox_c_closure && get_type(Closure2) == roblox_c_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonecfunction(L, 1);

					Closure1->c.f = (lua_CFunction)Closure2->c.f;
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;
					Closure1->env = (Table*)Closure2->env;

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->c.upvals[i], &Closure2->c.upvals[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == module_c_closure && get_type(Closure2) == module_c_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonecfunction(L, 1);
					Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));

					Handler::set(Closure1, Handler::get(Closure2));
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;
					Closure1->env = (Table*)Closure2->env;

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->c.upvals[i], &Closure2->c.upvals[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == module_c_wrap && get_type(Closure2) == module_c_wrap)
			{
				lua_clonecfunction(L, 1);
				Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));

				Handler::wraps::set(clvalue(index2addr(L, -1)), Handler::wraps::get(Closure1));
				Handler::wraps::set(Closure1, Handler::wraps::get(Closure2));

				Closure1->env = (Table*)Closure2->env;
			}

			else if (get_type(Closure1) == l_closure && get_type(Closure2) == l_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonefunction(L, 1);

					Closure1->l.p = (Proto*)Closure2->l.p;
					Closure1->c.f = (lua_CFunction)Closure2->c.f;
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;
					Closure1->env = (Table*)Closure2->env;
					Closure1->stacksize = Closure2->stacksize;

					for (int i = 0; i < NupVal; i++)
						setobj2n(L, &Closure1->l.uprefs[i], luaO_nilobject);

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->l.uprefs[i], &Closure2->l.uprefs[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == roblox_c_closure && get_type(Closure2) == module_c_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonecfunction(L, 1);

					Handler::set(Closure1, Handler::get(Closure2));

					Closure1->c.f = (lua_CFunction)Closure2->c.f;
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;
					Closure1->env = (Table*)Closure2->env;

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->c.upvals[i], &Closure2->c.upvals[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == roblox_c_closure && get_type(Closure2) == module_c_wrap)
			{
				lua_clonecfunction(L, 1);

				Handler::set(Closure1, Handler::get(Closure2));
				Handler::wraps::set(Closure1, Handler::wraps::get(Closure2));

				Closure1->c.f = (lua_CFunction)Closure2->c.f;
				Closure1->c.cont = (lua_Continuation)Closure2->c.cont;
				Closure1->env = (Table*)Closure2->env;
			}

			else if (get_type(Closure1) == roblox_c_closure && get_type(Closure2) == l_closure)
			{
				CClosureThingy(L, 2);
				lua_clonecfunction(L, 1);
				lua_ref(L, 2);

				Closure1->c.f = (lua_CFunction)Handler::cfunction_handler;
				Handler::set(Closure1, newcclosure_handler);
				Handler::wraps::set(Closure1, Closure2);
			}

			else if (get_type(Closure1) == module_c_closure && get_type(Closure2) == roblox_c_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonecfunction(L, 1);
					Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));

					Closure1->env = (Table*)Closure2->env;
					Closure1->c.f = (lua_CFunction)Closure2->c.f;
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->c.upvals[i], &Closure2->c.upvals[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == module_c_closure && get_type(Closure2) == module_c_wrap)
			{
				lua_clonecfunction(L, 1);
				Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));

				Handler::set(Closure1, newcclosure_handler);
				Handler::wraps::set(Closure1, Closure2);
			}

			else if (get_type(Closure1) == module_c_closure && get_type(Closure2) == l_closure)
			{
				lua_clonecfunction(L, 1);
				Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));
				lua_ref(L, 2);

				Handler::set(Closure1, newcclosure_handler);
				Handler::wraps::set(Closure1, Closure2);
			}

			else if (get_type(Closure1) == module_c_wrap && get_type(Closure2) == roblox_c_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonecfunction(L, 1);
					Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));
					Handler::wraps::set(clvalue(index2addr(L, -1)), Handler::wraps::get(Closure1));

					Closure1->env = (Table*)Closure2->env;
					Closure1->c.f = (lua_CFunction)Closure2->c.f;
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->c.upvals[i], &Closure2->c.upvals[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == module_c_wrap && get_type(Closure2) == module_c_closure)
			{
				if (NupVal >= NupVal2)
				{
					lua_clonecfunction(L, 1);
					Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));
					Handler::wraps::set(clvalue(index2addr(L, -1)), Handler::wraps::get(Closure1));

					Handler::set(Closure1, Handler::get(Closure2));

					Closure1->env = (Table*)Closure2->env;
					Closure1->c.cont = (lua_Continuation)Closure2->c.cont;

					for (int i = 0; i < NupVal2; i++)
						setobj2n(L, &Closure1->c.upvals[i], &Closure2->c.upvals[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}

			else if (get_type(Closure1) == module_c_wrap && get_type(Closure2) == l_closure)
			{
				lua_clonecfunction(L, 1);
				Handler::set(clvalue(index2addr(L, -1)), Handler::get(Closure1));
				Handler::wraps::set(clvalue(index2addr(L, -1)), Handler::wraps::get(Closure1));

				lua_ref(L, 2);
				Handler::wraps::set(Closure1, Closure2);
			}

			else if (get_type(Closure1) == l_closure && (get_type(Closure2) == roblox_c_closure || get_type(Closure2) == module_c_closure))
			{
				int hookRef = lua_ref(L, 2);

				lua_newtable(L);

				lua_newtable(L);

				lua_pushvalue(L, LUA_GLOBALSINDEX);
				lua_setfield(L, -2, "__index");
				lua_setmetatable(L, -2);
				lua_rawgeti(L, LUA_REGISTRYINDEX, hookRef);
				lua_setfield(L, -2, "abcdefg");

				const unsigned char bytecode[] = {


					0x06, 0x03, 0x01, 0x07, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x00, 0x01, 0x02, 0x00, 0x00,


					0x01, 0x02, 0x00, 0x08, 0xa3, 0x00, 0x00, 0x00, 0x2f, 0x00, 0x00, 0x00, 0x2f, 0x00, 0x00, 0x00,


					0xa4, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x40, 0xdd, 0x01, 0x00, 0x00, 0x9f, 0x00, 0x00, 0x00,


					0x82, 0x00, 0x00, 0x00, 0x02, 0x03, 0x01, 0x04, 0x00, 0x00, 0x00, 0x40, 0x00, 0x01, 0x00, 0x01,


					0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,


				};
				std::string bytecodeStr(reinterpret_cast<const char*>(bytecode), sizeof(bytecode));

				auto compressed = CompressBytecode(bytecodeStr);

				rcv::defs::LuaVM_Load(L, &compressed, "@z", 0);

				lua_pushvalue(L, -2);

				lua_setfenv(L, -2);
				Closure* newLClosure = lua_toclosure(L, -1);
				lua_ref(L, -1);

				Closure1->l.p = (Proto*)newLClosure->l.p;
				Closure1->env = (Table*)newLClosure->env;

				for (int i = 0; i < NupVal; i++)


					setobj2n(L, &Closure1->l.uprefs[i], luaO_nilobject);

				for (int i = 0; i < NupVal2; i++)


					setobj2n(L, &Closure1->l.uprefs[i], &Closure2->l.uprefs[i]);
			}

			else if (get_type(Closure1) == l_closure && get_type(Closure2) == module_c_wrap)
			{
				const Closure* l = Handler::wraps::get(Closure2);

				if (NupVal >= l->nupvalues)
				{
					lua_clonefunction(L, 1);

					Closure1->env = (Table*)l->env;
					Closure1->l.p = (Proto*)l->l.p;

					for (int i = 0; i < l->nupvalues; i++)
						setobj2n(L, &Closure1->l.uprefs[i], &l->l.uprefs[i]);
				}
				else
					luaL_error(L, "Cannot do anything with to much upvalues!");
			}
			else
				luaL_error(L, "Could not unhook");

			return 1;
		}

		auto iscclosure(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TFUNCTION);

			lua_pushboolean(rl, lua_iscfunction(rl, 1));
			return 1;
		}

		auto islclosure(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TFUNCTION);

			lua_pushboolean(rl, lua_isLfunction(rl, 1));
			return 1;
		}

		auto checkcaller(lua_State* rl) -> int
		{
			const auto script_ptr = *(std::uintptr_t*)((std::uintptr_t)((rl->userdata)) + 0x50);

			lua_pushboolean(rl, !script_ptr);
			return 1;
		}

		int loadstring(lua_State* L) {
			const char* src = luaL_checklstring(L, 1, nullptr);

			const char* name = luaL_optlstring(L, 2, oxorany("=Env"), nullptr);

			std::string source = std::string(src);

			std::string chunk_name = std::string(name);

			return Execution::Lua_LoadString(L, source, chunk_name);
		}
	}

	namespace Scripts {




		namespace HelpFunctions {
			std::optional<std::string> GetScriptBytecodeHandler(lua_State* L, void* udata, bool shouldDecompress) {
				std::uintptr_t script = (uintptr_t)udata;
				uintptr_t class_descriptor = *reinterpret_cast<uintptr_t*>(script + 0x18);
				std::string class_name = **reinterpret_cast<std::string**>(class_descriptor + 0x8);

				std::optional<std::string> protected_bytecode;

				if (!strcmp(class_name.c_str(), "ModuleScript")) {
					auto compressed_bytecode = *reinterpret_cast<std::string*>(*reinterpret_cast<std::uintptr_t*>(script + rcv::offsets::ModuleScriptBytecode) + 0x10);

					if (shouldDecompress) {
						return decompress(compressed_bytecode);;
					}
					else {
						return compressed_bytecode;
					}
				}

				if (!strcmp(class_name.c_str(), "LocalScript")) {
					auto compressed_bytecode = *reinterpret_cast<std::string*>(*reinterpret_cast<std::uintptr_t*>(script + rcv::offsets::LocalScriptBytecode) + 0x10);


					if (shouldDecompress) {
						return decompress(compressed_bytecode);;
					}
					else {
						return compressed_bytecode;
					}
				}

				return protected_bytecode;
			}
		}

		uintptr_t convert_identity_to_capability(uintptr_t Identity) {
			uintptr_t returnVal = NULL;

			switch (Identity)
			{
			case 4:
				returnVal = 0x2000000000000003LL;
				break;
			case 3:
				returnVal = 0x200000000000000BLL;
				break;
			case 5:
				returnVal = 0x2000000000000001LL;
				break;
			case 6:
				returnVal = 0x600000000000000BLL;
				break;
			case 8:
				returnVal = 0x200000000000003FLL;
				break;
			case 9:
				returnVal = 12LL;
				break;
			case 10:
				returnVal = 0x6000000000000003LL;
				break;
			case 11:
				returnVal = 0x2000000000000000LL;
				break;
			default:
				returnVal = 0LL;
				break;
			}
			return returnVal | IdentityCaps;
		};

		void set_thread_identity(lua_State* L, uintptr_t Identity) {
			uintptr_t identityStruct = rcv::defs::GetIdentityStruct(*reinterpret_cast<uintptr_t*>(rcv::IdentityPtr));
			if (!identityStruct)
				return;

			Memory::SetThreadIdentity((uintptr_t)L, Identity);
			Memory::SetThreadCapabilities((uintptr_t)L, convert_identity_to_capability(Identity));

			*reinterpret_cast<int32_t*>(identityStruct) = (int32_t)(Identity);
			*reinterpret_cast<uintptr_t*>(identityStruct + 32) = convert_identity_to_capability(Identity);
		}

		int getidentity(lua_State* L) {
			const auto ExtraSpace = (uintptr_t)L->userdata;

			lua_pushnumber(L, *(__int64*)(ExtraSpace + rcv::offsets::Identity));

			return 1;
		}

		int setidentity(lua_State* L) {
			int identity = lua_tonumber(L, 1);
			if (identity > 8) {
				luaL_error(L, oxorany("You cannot set the identity higher than 8!"));
			}
			set_thread_identity(L, identity);
			return 0;
		}

		int getgenv(lua_State* L)
		{
			lua_pushvalue(L, LUA_ENVIRONINDEX);
			return 1;
		}

		int getreg(lua_State* L)
		{
			lua_pushvalue(L, LUA_REGISTRYINDEX);
			return 1;
		}

		int getgc(lua_State* L) {
			bool Table = luaL_optboolean(L, 1, 0);

			int idx = 0;
			lua_newtable(L);

			global_State* global = L->global;
			auto cur_page = global->allgcopages;
			auto old_gcstate = global->gcstate;
			global->gcstate = -1;

			while (cur_page)
			{
				char* start = nullptr;
				char* end = nullptr;
				auto block = 0;
				auto size = 0;

				luaM_getpagewalkinfo(cur_page, &start, &end, &block, &size);

				for (auto pos = start; pos != end; pos += size)
				{
					if (auto&& gco = reinterpret_cast<GCObject*>(pos); gco && gco->gch.tt == LUA_TFUNCTION || (Table && (gco->gch.tt == LUA_TTABLE || gco->gch.tt == LUA_TUSERDATA))) {
						if (isdead(L->global, gco)) {
							continue;
						}

						L->top->value.p = gco;
						L->top->tt = gco->cl.tt;
						incr_top(L);
						lua_rawseti(L, -2, ++idx);
					}
				}

				cur_page = cur_page->listnext;
			}


			global->gcstate = old_gcstate;

			return 1;
		}

		int filtergc1(lua_State* L) {
			std::string filter_type = luaL_checkstring(L, 1);
			bool return_one = lua_toboolean(L, 3);

			lua_newtable(L);
			int idx = 0;

			global_State* global = L->global;
			auto cur_page = global->allgcopages;
			auto old_gcstate = global->gcstate;
			global->gcstate = -1;

			while (cur_page) {
				char* start = nullptr;
				char* end = nullptr;
				auto block = 0;
				auto size = 0;

				luaM_getpagewalkinfo(cur_page, &start, &end, &block, &size);

				for (auto pos = start; pos != end; pos += size) {
					auto gco = reinterpret_cast<GCObject*>(pos);
					if (!gco || isdead(L->global, gco)) continue;

					bool match = false;

					if (filter_type == "function" && gco->gch.tt == LUA_TFUNCTION) {
						Closure* cl = reinterpret_cast<Closure*>(gco);
						if (!cl || !cl->l.p) continue;

						lua_pushvalue(L, 2);

						lua_getfield(L, -1, "Constants");
						if (lua_istable(L, -1) && cl->l.p->sizek > 0) {
							lua_pushnil(L);
							while (lua_next(L, -2)) {
								bool found = false;

								for (int i = 0; i < cl->l.p->sizek; i++) {
									const TValue* k = &cl->l.p->k[i];
									if (!k) continue;

									if (luaA_toobject(L, -2) && luaO_rawequalObj(k, luaA_toobject(L, -2))) {
										found = true;
										break;
									}
								}

								if (!found) {
									match = false;
									lua_pop(L, 2);
									break;
								}
								match = true;
								lua_pop(L, 1);
							}
						}
						lua_pop(L, 2);

					}
					else if (filter_type == "table" && gco->gch.tt == LUA_TTABLE) {
						lua_pushvalue(L, 2);
						lua_getfield(L, -1, "Keys");

						if (lua_istable(L, -1)) {
							lua_pushnil(L);
							while (lua_next(L, -2)) {
								lua_pushvalue(L, -2);
								if (!lua_rawget(L, -5)) {
									match = false;
									lua_pop(L, 2);
									break;
								}
								lua_pop(L, 2);
							}
							match = true;
						}
						lua_pop(L, 2);
					}

					if (match) {
						L->top->value.p = gco;
						L->top->tt = gco->gch.tt;
						incr_top(L);
						lua_rawseti(L, -2, ++idx);

						if (return_one) {
							global->gcstate = old_gcstate;
							return 1;
						}
					}
				}

				cur_page = cur_page->listnext;
			}

			global->gcstate = old_gcstate;

			return 1;
		}

		int gettenv(lua_State* L) {
			luaL_checktype(L, 1, LUA_TTHREAD);
			lua_State* ls = (lua_State*)lua_topointer(L, 1);
			Table* tab = hvalue(luaA_toobject(ls, LUA_GLOBALSINDEX));

			sethvalue(L, L->top, tab);
			L->top++;

			return 1;
		}

		int getrenv(lua_State* L) {
			setobj(L, L->top, index2addr(L->global->mainthread, LUA_GLOBALSINDEX));
			incr_top(L);
			return 1;
		}

		int gethui(lua_State* L)
		{
			lua_getfield(L, LUA_GLOBALSINDEX, "game");
			lua_getfield(L, -1, "CoreGui");
			return 1;
		}

		auto setclipboard(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TSTRING);

			std::string content = lua_tostring(rl, 1);

			HGLOBAL hMem = GlobalAlloc(GMEM_MOVEABLE, content.size() + 1);
			memcpy(GlobalLock(hMem), content.data(), content.size());
			GlobalUnlock(hMem);
			OpenClipboard(0);
			EmptyClipboard();
			SetClipboardData(CF_TEXT, hMem);
			CloseClipboard();
			return 0;
		}

		auto getclipboard(lua_State* rl) -> int
		{
			OpenClipboard(NULL);
			std::string clipboard = reinterpret_cast<char*>(GetClipboardData(CF_TEXT));

			lua_pushlstring(rl, clipboard.data(), clipboard.length());
			return 1;
		}

		auto identifyexecutor(lua_State* rl) -> int
		{
			lua_pushstring(rl, oxorany("Env"));
			lua_pushstring(rl, ("2.0"));
			return 2;
		}

		std::mutex teleport_mutex;

		int queue_on_teleport(lua_State* L) {
			const auto script = luaL_checkstring(L, 1);

			std::unique_lock< std::mutex > locker{ teleport_mutex };

			Environment::teleport_queue_script.push(script);

			return 0;
		}

		int setfps(lua_State* L) {
			luaL_checktype(L, 1, LUA_TNUMBER);

			double fps = lua_tonumber(L, 1);

			*reinterpret_cast<int32_t*>(rcv::TaskSchedulerTargetFps) = fps;

			return 0;
		}

		int getfps(lua_State* L) {
			std::optional<double> fps = *reinterpret_cast<int32_t*>(rcv::TaskSchedulerTargetFps);

			if (fps.has_value()) {
				lua_pushnumber(L, fps.value());
			}
			else {
				lua_pushnumber(L, 0);
			}

			return 1;
		}

		auto getcallingscript(lua_State* rl) -> int
		{

			uintptr_t userdata = *reinterpret_cast<uintptr_t*>((__int64)rl + 120);
			__int64 scriptptr = *reinterpret_cast<uintptr_t*>(userdata + 0x50);

			if (scriptptr > 0) {
				rcv::defs::PushInstance(rl, reinterpret_cast<__int64*>(userdata + 0x50));
			}
			else {
				lua_pushnil(rl);
			}



			return 1;
		}

		int getobjects(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TSTRING);

			lua_getglobal(L, ("game"));
			lua_getfield(L, -1, ("GetService"));

			lua_pushvalue(L, -2);
			lua_pushstring(L, ("InsertService"));
			lua_pcall(L, 2, 1, 0);

			lua_getfield(L, -1, ("LoadLocalAsset"));

			lua_pushvalue(L, -2);
			lua_pushvalue(L, 2);
			lua_pcall(L, 2, 1, 0);

			if (lua_type(L, -1) == LUA_TSTRING) {
				luaL_error(L, lua_tostring(L, -1));
			}

			lua_createtable(L, 0, 0);

			lua_pushvalue(L, -2);
			lua_rawseti(L, -2, 1);

			return 1;
		}

		auto getloadedmodules(lua_State* rl) -> int
		{
			std::vector<std::shared_ptr<uintptr_t>> instances;

			const auto loaded_modules = *reinterpret_cast<std::set<std::weak_ptr<uintptr_t>>*>(Memory::GetScriptContext() + 1400 + 64);
			for (auto module : loaded_modules)
			{
				if (!module.expired())
				{
					instances.push_back(module.lock());
				}
			}

			lua_newtable(rl);

			for (int i = 0; i < instances.size(); i++)
			{
				using epushinstance_t = void(__fastcall*)(__int64 state, std::shared_ptr<std::uintptr_t>& instance);
				static epushinstance_t rbx_e_pushinstance = reinterpret_cast<epushinstance_t>(rcv::PushInstance);

				lua_pushinteger(rl, i + 1);
				rbx_e_pushinstance((__int64)rl, instances[i]);
				lua_settable(rl, -3);
			}

			return 1;
		}

		int getloadedmodules1(lua_State* L)
		{
			lua_newtable(L);

			typedef struct {
				lua_State* pLua;
				int itemsFound;
				std::map< uintptr_t, bool > map;
			} GCOContext;

			auto gcCtx = GCOContext{ L, 0 };

			const auto ullOldThreshold = L->global->GCthreshold;
			L->global->GCthreshold = SIZE_MAX;

			luaM_visitgco(L, &gcCtx, [](void* ctx, lua_Page* pPage, GCObject* pGcObj) -> bool {
				const auto pCtx = static_cast<GCOContext*>(ctx);
				const auto ctxL = pCtx->pLua;

				if (isdead(ctxL->global, pGcObj))
					return false;

				if (const auto gcObjType = pGcObj->gch.tt;
					gcObjType == LUA_TFUNCTION) {
					ctxL->top->value.gc = pGcObj;
					ctxL->top->tt = gcObjType;
					ctxL->top++;

					lua_getfenv(ctxL, -1);

					if (!lua_isnil(ctxL, -1)) {
						lua_getfield(ctxL, -1, "script");

						if (!lua_isnil(ctxL, -1)) {
							uintptr_t script_addr = *(uintptr_t*)lua_touserdata(ctxL, -1);

							std::string class_name = **(std::string**)(*(uintptr_t*)(script_addr + 0x18) + 0x8);

							if (pCtx->map.find(script_addr) == pCtx->map.end() && class_name == "ModuleScript") {
								pCtx->map.insert({ script_addr, true });
								lua_rawseti(ctxL, -4, ++pCtx->itemsFound);
							}
							else {
								lua_pop(ctxL, 1);
							}
						}
						else {
							lua_pop(ctxL, 1);
						}
					}

					lua_pop(ctxL, 2);
				}
				return false;
				});

			L->global->GCthreshold = ullOldThreshold;

			return 1;
		}

		int getsenv(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);
			uintptr_t script_instance = *(uintptr_t*)lua_touserdata(L, 1);

			lua_getglobal(L, ("typeof"));
			lua_pushvalue(L, 1);
			lua_call(L, 1, 1);
			const bool isInstance = (strcmp(lua_tolstring(L, -1, 0), ("Instance")) == 0);
			lua_pop(L, 1);

			if (!isInstance)
				luaL_argerror(L, 1, ("Did not get a Instance"));

			lua_getfield(L, 1, ("ClassName"));
			const char* class_name = lua_tolstring(L, -1, NULL);

			lua_pop(L, 1);

			//lua_settop(L, 0);

			if (strcmp(class_name, "LocalScript") && strcmp(class_name, "ModuleScript")) {
				luaL_argerror(L, 1, ("LocalScript or ModuleScript required!"));
			}

			if (!strcmp(class_name, "LocalScript")) {
				auto node = *reinterpret_cast<Node_t**>(script_instance + 0x1A0);

				if (node == nullptr)
				{
					lua_pushnil(L);
					return 1;
				}

				auto wtr = node->wtr;
				if (wtr == nullptr)
				{
					lua_pushnil(L);
					return 1;
				}

				for (auto it = wtr; it; it = it->next)
				{
					auto thref = it->liveThreadRef;
					if (thref == nullptr)
					{
						continue;
					}

					auto thread = thref->th;
					if (thread == nullptr)
					{
						continue;
					}

					const auto extraspace = reinterpret_cast<int64_t>(lua_getthreaddata(thread));

					uintptr_t thread_scr;

					if (extraspace)
					{
						thread_scr = *(uintptr_t*)(extraspace + rcv::offsets::Script);
					}

					if (thread_scr)
					{
						if (script_instance == thread_scr)
						{
							lua_pushvalue(thread, LUA_GLOBALSINDEX);
							lua_xmove(thread, L, 1);
							return 1;
						}
					}
					else
					{
						continue;
					}
				}
			}
			else if (!strcmp(class_name, "ModuleScript")) {
				+
					lua_getglobal(L, "getfenv");
				{
					*(bool*)(rcv::EnableLoadModule) = true;

					lua_getglobal(L, "debug");
					lua_getfield(L, -1, "loadmodule");
					{
						lua_pushvalue(L, 1);
					}
					lua_call(L, 1, 1);
					lua_remove(L, -2);

					*(bool*)(rcv::EnableLoadModule) = false;
				}
				lua_call(L, 1, 1);

				if (!lua_isnoneornil(L, -1))
				{
					return 1;
				}
			}

			lua_pushnil(L);
			return 1;
		}

		int getrunningscripts(lua_State* L) {
			std::map< uintptr_t, bool > map;

			lua_pushvalue(L, LUA_REGISTRYINDEX);

			lua_newtable(L);

			lua_pushnil(L);

			auto c = 0u;
			while (lua_next(L, -3))
			{
				if (lua_isthread(L, -1))
				{
					const auto thread = lua_tothread(L, -1);

					if (thread)
					{
						if (const auto script_ptr = reinterpret_cast<std::uintptr_t>(thread->userdata) + 0x50; *reinterpret_cast<std::uintptr_t*>(script_ptr))
						{
							if (map.find(*(uintptr_t*)script_ptr) == map.end())
							{
								map.insert({ *(uintptr_t*)script_ptr, true });

								rcv::defs::PushInstance(L, (void*)script_ptr);

								lua_rawseti(L, -4, ++c);
							}
						}
					}
				}

				lua_pop(L, 1);
			}

			return 1;
		}

		auto firetouchinterest(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TUSERDATA);
			luaL_checktype(rl, 2, LUA_TUSERDATA);
			luaL_checktype(rl, 3, LUA_TNUMBER);

			uintptr_t part = *(uintptr_t*)lua_touserdata(rl, 1);
			uintptr_t transmitter = *(uintptr_t*)lua_touserdata(rl, 2);
			int state = lua_tointeger(rl, 3);

			uintptr_t part_primitive = *reinterpret_cast<uintptr_t*>(part + 0x168);
			uintptr_t transmitter_primitive = *reinterpret_cast<uintptr_t*>(transmitter + 0x168);

			if (!part_primitive || !transmitter_primitive || *(uintptr_t*)(part_primitive + 464) != *(uintptr_t*)(transmitter_primitive + 464))
				luaL_error(rl, "New overlap in different world.");

			rcv::defs::Touch(*reinterpret_cast<uintptr_t*>(part_primitive + 464), part_primitive, transmitter_primitive, state);
			return 0;
		}

		auto fireclickdetector(lua_State* L) -> int {
			luaL_stackcheck(L, 1, 3, checkType(L, 1, LUA_TUSERDATA));

			const auto detector = *reinterpret_cast<std::uintptr_t*>(lua_touserdata(L, 1));
			const auto distance = static_cast<float>(luaL_optnumber(L, 2, 0));
			const char* clickType = static_cast<const char*>(lua_tostring(L, 3));

			lua_getglobal(L, "game");
			lua_getfield(L, -1, "GetService");
			lua_pushvalue(L, -2);
			lua_pushstring(L, "Players");
			lua_pcall(L, 2, 1, 0);
			lua_getfield(L, -1, "LocalPlayer");

			const auto player = *reinterpret_cast<std::uintptr_t*>(lua_touserdata(L, -1));
			lua_pop(L, 3);

			rcv::defs::ClickDetector(detector, distance, player, clickType);

			lua_pushboolean(L, true);
			return 1;
		}


		auto fireproximityprompt(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TUSERDATA);

			lua_getglobal(rl, ("typeof"));
			lua_pushvalue(rl, 1);
			lua_call(rl, 1, 1);
			const bool isInstance = (strcmp(lua_tolstring(rl, -1, 0), ("Instance")) == 0);
			lua_pop(rl, 1);

			if (!isInstance)
				luaL_argerror(rl, 1, ("Expected Instance"));

			lua_getfield(rl, 1, ("IsA"));
			lua_pushvalue(rl, 1);
			lua_pushstring(rl, ("ProximityPrompt"));
			lua_call(rl, 2, 1);
			const bool isExpectedClass = lua_toboolean(rl, -1);
			lua_pop(rl, 1);

			if (!isExpectedClass)
				luaL_argerror(rl, 1, ("Expected an ProximityPrompt"));

			reinterpret_cast<int(__thiscall*)(std::uintptr_t)>(rcv::ProximityPrompt)(*reinterpret_cast<std::uintptr_t*>(lua_touserdata(rl, 1)));
			return 0;
		}

		std::string DecompressBytecode(const std::string& compressed) {
			uint8_t hash[4];
			memcpy(hash, compressed.data(), 4);

			const char* bcode_magic = oxorany("RSB1");
			for (auto i = 0; i < 4; i++)
			{
				hash[i] ^= bcode_magic[i];
				hash[i] -= i * 41;
			}

			std::vector<uint8_t> compressed_bcode(compressed.begin(), compressed.end());
			for (size_t i = 0; i < compressed_bcode.size(); i++)
				compressed_bcode[i] ^= hash[i % 4] + i * 41;

			int bcode_len;
			memcpy(&bcode_len, compressed_bcode.data() + 4, 4);

			std::vector<std::uint8_t> bcode(bcode_len);
			if (ZSTD_decompress(bcode.data(), bcode_len, compressed_bcode.data() + 8, compressed_bcode.size() - 8) != bcode_len) {
				return "";
			}
			else {
				return std::string(bcode.begin(), bcode.end());
			}

			return "";
		}

		std::string ReadByteCode(std::uint64_t Address) {
			std::uintptr_t str = Address + 0x10;
			std::uintptr_t data;

			if (*reinterpret_cast<std::size_t*>(str + 0x18) > 0xf) {
				data = *reinterpret_cast<std::uintptr_t*>(str);
			}
			else {
				data = str;
			}

			std::string BOOOHOOOOOOOO;
			std::size_t len = *reinterpret_cast<std::size_t*>(str + 0x10);
			BOOOHOOOOOOOO.reserve(len);

			for (unsigned i = 0; i < len; i++) {
				BOOOHOOOOOOOO += *reinterpret_cast<char*>(data + i);
			}

			return BOOOHOOOOOOOO;
		}

		std::string RequestBytecode(std::uintptr_t scriptPtr) {
			uintptr_t code[0x4];
			std::memset(code, 0, sizeof(code));

			rcv::defs::RequestCode((std::uintptr_t)code, scriptPtr);

			std::uintptr_t bytecodePtr = code[1];

			if (!bytecodePtr) { return oxorany("Error while getting bytecode"); }

			std::string Bytecode = ReadByteCode(bytecodePtr);
			if (Bytecode.size() <= 8) { return oxorany("Error while getting bytecode"); }

			std::string DecompressedBytecode = DecompressBytecode(Bytecode);
			if (DecompressedBytecode.size() <= 8) { return oxorany("Error while getting bytecode"); }

			return DecompressedBytecode;
		};

		int getscriptbytecode(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);

			const auto scriptPtr = *(uintptr_t*)lua_topointer(L, 1);
			const auto scriptCode = RequestBytecode(scriptPtr);

			lua_pushlstring(L, scriptCode.data(), scriptCode.size());
			return 1;
		}

		__forceinline int getfunctionbytecode(lua_State* L) {
			luaL_checktype(L, 1, LUA_TFUNCTION);

			Closure* cl = (Closure*)lua_topointer(L, 1);
			Proto* p = (Proto*)cl->l.p;
			// so first when the funcs are the same it would say it isn't since the time when it got created and stuff were different which now is fixed.
			uint8_t nupvalues = cl->nupvalues;

			std::string result =
				std::to_string((int)p->sizep) + "," +
				std::to_string((int)p->sizelocvars) + "," +
				std::to_string((int)p->sizeupvalues) + "," +
				std::to_string((int)p->sizek) + "," +
				std::to_string((int)p->sizelineinfo) + "," +
				std::to_string((int)p->linegaplog2) + "," +
				std::to_string((int)p->sizetypeinfo) + "," +
				std::to_string((int)p->numparams) + "," +
				std::to_string((int)p->is_vararg) + "," +
				std::to_string((int)p->sizecode) + "," +
				std::to_string(nupvalues);

			for (int i = 0; i < p->sizecode; ++i) {
				result += "," + std::to_string(p->code[i]);
			}

			std::string hash;
			CryptoPP::SHA384 sha384;
			CryptoPP::StringSource(result, true,
				new CryptoPP::HashFilter(sha384, new CryptoPP::HexEncoder(new CryptoPP::StringSink(hash))));

			lua_pushstring(L, hash.c_str());
			return 1;
		}

		int getcallbackvalue(lua_State* L)
		{
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TSTRING);

			auto Instance = *(uintptr_t*)lua_touserdata(L, 1);

			int Atom;
			auto Property = lua_tostringatom(L, 2, &Atom);

			const auto KTable = (uintptr_t*)rcv::KTable;
			auto Descriptor = KTable[Atom];
			if (!Descriptor) {
				lua_pushnil(L);
				return 1;
			}

			auto ClassDescriptor = *(uintptr_t*)(Instance + 0x18);
			const auto PropertyDescriptor = rcv::defs::GetProperty(ClassDescriptor + 0x3B0, &Descriptor);
			if (!PropertyDescriptor)
				luaL_error(L, oxorany("Invalid property"));

			const auto PropertyType = *reinterpret_cast<int32_t*>((uintptr_t)PropertyDescriptor + 0x8);
			if (PropertyType != 4)
				luaL_error(L, oxorany("Invalid property"));

			const auto callbackBaseAddress = (Instance + *(uintptr_t*)(*PropertyDescriptor + 0x78));
			const auto callbackExists = *reinterpret_cast<uintptr_t*>(callbackBaseAddress + 0x38);
			if (!callbackExists) {
				lua_pushnil(L);
				return 1;
			}

			const auto callbackDataAddress = *reinterpret_cast<uintptr_t*>(callbackBaseAddress + 0x18);
			const auto callbackMetadataAddress = callbackDataAddress ? *reinterpret_cast<uintptr_t*>(callbackDataAddress + 0x38) : NULL;
			const auto callbackHandlerAddress = callbackMetadataAddress ? *reinterpret_cast<uintptr_t*>(callbackMetadataAddress + 0x28) : NULL;
			const auto callbackId = callbackHandlerAddress ? *reinterpret_cast<int*>(callbackHandlerAddress + 0x14) : NULL;
			if (!callbackId) {
				lua_pushnil(L);
				return 1;
			}

			lua_getref(L, callbackId);
			if (lua_isfunction(L, -1))
				return 1;

			lua_pop(L, 1);
			lua_pushnil(L);
			return 1;
		}

		static uintptr_t Caps = 0xFFFFFFFFFFFFFFFF;

		std::string NoDecompressRequestBytecode(std::uintptr_t scriptPtr) {
			uintptr_t code[0x4];
			std::memset(code, 0, sizeof(code));

			rcv::defs::RequestCode((std::uintptr_t)code, scriptPtr);

			std::uintptr_t bytecodePtr = code[1];

			if (!bytecodePtr) { return oxorany("Error while getting bytecode"); }

			std::string Bytecode = ReadByteCode(bytecodePtr);
			if (Bytecode.size() <= 8) { return oxorany("Error while getting bytecode"); }

			return Bytecode;
		};

		inline void SetCapabilitiesR(Proto* Proto, uintptr_t* CapFlags)
		{
			if (!Proto)
				return;

			Proto->userdata = CapFlags;
			for (int i = 0; i < Proto->sizep; ++i)
				SetCapabilitiesR(Proto->p[i], CapFlags);

			return;
		}

		std::string getClassName(lua_State* L, int idx) {
			int originalArgCount = lua_gettop(L);
			lua_getfield(L, idx, "ClassName");
			std::string object_ClassName = luaL_checklstring(L, -1, nullptr);
			lua_pop(L, lua_gettop(L) - originalArgCount);

			return object_ClassName;
		};

		__forceinline static void raise_proto(Proto* proto)
		{
			proto->userdata = &Caps;
			for (auto i = 0; i < proto->sizep; i++) {
				raise_proto(proto->p[i]);
			}
		}

		int getscriptclosure(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);

			const auto scriptPtr = *(uintptr_t*)lua_topointer(L, 1);
			std::string scriptCode = NoDecompressRequestBytecode(scriptPtr);

			lua_State* L2 = lua_newthread(L);
			luaL_sandboxthread(L2);

			Memory::SetThreadCapabilities((uintptr_t)L2, Caps);

			lua_pushvalue(L, 1);
			lua_xmove(L, L2, 1);
			lua_setglobal(L2, oxorany("script"));

			int result = rcv::defs::LuaVM_Load(L2, &scriptCode, "", 0);

			if (result == LUA_OK) {
				Closure* cl = clvalue(luaA_toobject(L2, -1));

				if (cl) {
					Proto* p = cl->l.p;
					if (p) {
						Execution::SetProtoCaps(p, &Caps);
					}
				}

				lua_pop(L2, lua_gettop(L2));
				lua_pop(L, lua_gettop(L));

				setclvalue(L, L->top, cl);
				incr_top(L);

				return 1;
			}

			lua_pushnil(L);
			return 1;
		};

		template<typename T>
		static std::string hash_with_algo(const std::string& Input)
		{
			T Hash;
			std::string Digest;

			CryptoPP::StringSource SS(Input, true,
				new CryptoPP::HashFilter(Hash,
					new CryptoPP::HexEncoder(
						new CryptoPP::StringSink(Digest), false
					)));

			return Digest;
		}

		auto getscripthash(lua_State* L) -> int {
			uintptr_t script = *reinterpret_cast<uintptr_t*>(lua_touserdata(L, 1));
			const char* classname = *reinterpret_cast<const char**>(*reinterpret_cast<uintptr_t*>(script + 24) + 8);
			std::string compressed_bytecode;

			compressed_bytecode = RequestBytecode(script);

			std::string data = hash_with_algo<CryptoPP::SHA384>(compressed_bytecode);
			lua_pushlstring(L, data.c_str(), data.size());
			return 1;
		}

		int lz4compress(lua_State* L) {
			luaL_checktype(L, 1, LUA_TSTRING);

			std::string input = lua_tostring(L, 1);
			std::string output;

			output.resize(LZ4_compressBound(input.size()));

			int compressedSize = LZ4_compress_default(input.c_str(), output.data(), input.size(), output.size());

			if (compressedSize <= 0) {
				lua_pushnil(L);
				return 1;
			}

			output.resize(compressedSize);

			lua_pushlstring(L, output.c_str(), output.size());
			return 1;
		}

		int lz4decompress(lua_State* L) {
			luaL_checktype(L, 1, LUA_TSTRING);

			std::string input = lua_tostring(L, 1);
			std::string output;

			output.resize(input.size() * 255);

			int decompressedSize = LZ4_decompress_safe(input.c_str(), output.data(), input.size(), output.size());

			if (decompressedSize <= 0) {
				lua_pushnil(L);
				return 1;
			}

			output.resize(decompressedSize);

			lua_pushlstring(L, output.c_str(), output.size());

			return 1;
		}
	}

	namespace WebSocket {
		class lua_websocket
		{
		private:
			ix::WebSocket socket = ix::WebSocket(); // Websocket object 

		public:
			lua_State* L; // socket lua thread

			std::string mUrl;
			int L_refid; // socket lua thread Registry Reference ID ( lua_ref )
			int onmessage_refid; // Registry Reference ID ( lua_ref ) for OnMessage
			int onclose_refid; // Registry Reference ID ( lua_ref ) for OnClose
			int onerr_ref; // Registry Reference ID ( lua_ref ) for OnError

			~lua_websocket() {

				//LOGD("lua_websocket %p is being stopped!", this);

				socket.stop();
			}

			auto stop() -> void {

				// LOGD("lua_websocket %p is being stopped!", this);

				socket.stop();
			}

			auto send_msg(const std::string& msg) -> void
			{
				socket.sendText(msg.c_str());
			}

			auto is_connected() const -> bool
			{
				return socket.getReadyState() == ix::ReadyState::Open;
			}

			auto get_url() const -> std::string
			{
				return mUrl;
			}

			auto setupSocket(const std::string& url) -> bool;
		};

		auto lua_websocket::setupSocket(const std::string& url) -> bool
		{
			std::string HWID = GetHwid().value();

			ix::SocketTLSOptions tlsOptions;
			tlsOptions.caFile = "ca.crt";
			socket.setTLSOptions(tlsOptions);

			socket.setUrl(url.c_str());
			socket.enablePong();

			ix::WebSocketHttpHeaders headers;
			headers.insert({ "User-Agent", "Roblox/WinInet" });
			headers.insert({ "ExploitIdentifier", "Env" });
			headers.insert({ "Exploit-Guid", HWID });
			headers.insert({ ("Env-Fingerprint"), HWID });
			socket.setExtraHeaders(headers);
			socket.setHandshakeTimeout(15);
			socket.setOnMessageCallback([this](const ix::WebSocketMessagePtr& msg)
				{
					switch (msg->type)
					{
					case ix::WebSocketMessageType::Message:
					{
						if (onmessage_refid)
						{
							lua_getref(L, onmessage_refid);
							lua_getfield(L, -1, "Fire");
							{
								lua_pushvalue(L, -2);
								lua_pushlstring(L, msg->str.c_str(), msg->str.size());
							}
							lua_pcall(L, 2, 0, 0);
							lua_pop(L, 1);
						}

						break;
					}

					case ix::WebSocketMessageType::Close:
					{
						if (onclose_refid)
						{
							lua_getref(L, onclose_refid);
							lua_getfield(L, -1, "Fire");
							{
								lua_pushvalue(L, -2);
							}
							lua_pcall(L, 1, 0, 0);
							lua_pop(L, 1);

							lua_unref(L, onmessage_refid);
							lua_unref(L, onclose_refid);
							lua_unref(L, onerr_ref);
							lua_unref(L, L_refid);
						}

						break;
					}

					case ix::WebSocketMessageType::Error:
					{
						std::stringstream ss;
						ss << "Error: " << msg->errorInfo.reason << "\n";
						ss << "#retries: " << msg->errorInfo.retries << "\n";
						ss << "Wait time(ms): " << msg->errorInfo.wait_time << "\n";
						ss << "HTTP Status: " << msg->errorInfo.http_status << "\n";

						if (onerr_ref)
						{
							lua_getref(L, onerr_ref);
							lua_getfield(L, -1, "Fire");
							{
								lua_pushvalue(L, -2);
								lua_pushlstring(L, ss.str().c_str(), ss.str().size());
							}
							lua_call(L, 2, 0);
							lua_pop(L, 1);
						}

						luaL_error(L, ("WebSocket Error: %s"), ss.str().c_str());
						break;
					}

					default: break;
					}
				});

			if (!socket.connect(30).success)
			{
				return false;
			}

			socket.start();
			return true;
		}

		std::unordered_map<void*, std::shared_ptr<lua_websocket>> socket_map{ };

		static int websocket_send(lua_State* ls)
		{
			luaL_checktype(ls, 1, LUA_TUSERDATA);
			luaL_checktype(ls, 2, LUA_TSTRING);

			void* userdata = lua_touserdatatagged(ls, lua_upvalueindex(1), 69);
			if (socket_map.find(userdata) == socket_map.end())
			{
				luaL_error(ls, "%s", ("Could not find socket"));
			}

			auto socket = socket_map[userdata];

			if (socket->is_connected())
			{
				socket->send_msg(lua_tostring(ls, 2));
			}
			else
			{
				socket_map.erase(userdata);
			}

			return 0;
		}

		static int websocket_close(lua_State* ls)
		{
			luaL_checktype(ls, 1, LUA_TUSERDATA);

			void* userdata = lua_touserdatatagged(ls, lua_upvalueindex(1), 69);
			if (socket_map.find(userdata) == socket_map.end())
			{
				luaL_error(ls, "%s", ("Could not find socket"));
			}

			auto socket = socket_map[userdata];

			socket->stop();

			socket_map.erase(userdata);

			return 0;
		}

		static int websocket_index(lua_State* ls)
		{
			void* userdata = lua_touserdatatagged(ls, 1, 69);
			const char* key = lua_tolstring(ls, 2, NULL);

			if (socket_map.find(userdata) == socket_map.end())
			{
				luaL_error(ls, "Could not find socket");
			}

			auto socket = socket_map[userdata];

			if (strcmp(key, "Url") == 0)
			{
				lua_pushstring(ls, socket->get_url().c_str());
				return 1;
			}
			else if (strcmp(key, "Send") == 0)
			{
				lua_pushvalue(ls, 1);
				lua_pushcclosure(ls, websocket_send, 0, 1);

				return 1;
			}
			else if (strcmp(key, "Close") == 0)
			{
				lua_pushvalue(ls, 1);
				lua_pushcclosure(ls, websocket_close, 0, 1);

				return 1;
			}
			else if (strcmp(key, "OnMessage") == 0)
			{
				lua_getref(ls, socket->onmessage_refid);
				lua_getfield(ls, -1, "Event");

				return 1;
			}
			else if (strcmp(key, "OnClose") == 0)
			{
				lua_getref(ls, socket->onclose_refid);
				lua_getfield(ls, -1, "Event");

				return 1;
			}
			else if (strcmp(key, "OnError") == 0)
			{
				lua_getref(ls, socket->onerr_ref);
				lua_getfield(ls, -1, "Event");

				return 1;
			}

			return 0;
		}

		int websocket_connect(lua_State* ls) {
			luaL_checktype(ls, 1, LUA_TSTRING);
			std::string url = lua_tostring(ls, 1);

			if (url.find("ws://") != 0 && url.find("wss://") != 0 || url == "ws://" || url == "wss://")
				luaL_argerror(ls, 1, "Invalid protocol specified (expected 'ws://' or 'wss://')");

			lua_getglobal(ls, ("Instance"));
			lua_getfield(ls, -1, ("new"));
			{
				lua_pushstring(ls, ("BindableEvent"));
			}
			if (lua_pcall(ls, 1, 1, 0))
			{
				auto error_str = lua_tostring(ls, -1);
				//luaL_error(ls, "%s", error_str);
			}

			const auto ud = reinterpret_cast<std::int64_t>(lua_touserdata(ls, -1));

			lua_remove(ls, -2);

			const auto onmessage_refid = lua_ref(ls, -1);

			lua_getglobal(ls, ("Instance"));
			lua_getfield(ls, -1, ("new"));
			{
				lua_pushstring(ls, ("BindableEvent"));
			}
			if (lua_pcall(ls, 1, 1, 0))
			{
				auto error_str = lua_tostring(ls, -1);

				//luaL_error(ls, "%s", error_str);
			}

			const auto udddd = reinterpret_cast<std::int64_t>(lua_touserdata(ls, -1));

			lua_remove(ls, -2);
			const auto onclose_refid = lua_ref(ls, -1);

			lua_getglobal(ls, ("Instance"));
			lua_getfield(ls, -1, ("new"));
			{
				lua_pushstring(ls, ("BindableEvent"));
			}
			if (lua_pcall(ls, 1, 1, 0))
			{
				auto error_str = lua_tostring(ls, -1);

				//luaL_error(ls, "%s", error_str);
			}

			const auto udd = reinterpret_cast<std::int64_t>(lua_touserdata(ls, -1));

			lua_remove(ls, -2);
			const auto onerr_ref = lua_ref(ls, -1);

			return Scheduler::YieldExecution(ls, [onmessage_refid, onerr_ref, onclose_refid, url]() -> std::function<int(lua_State*)> {
				const auto socket = std::make_shared< lua_websocket >();
				if (!socket->setupSocket(url))
				{
					return ([url](lua_State* ls) -> int
						{
							//atlantis::yielding::resume_error(ls, ("Failed to connect websocket to URL ('%s')!"), url.c_str());
							return 0;
						});
				}

				return ([onclose_refid, onerr_ref, onmessage_refid, socket](lua_State* ls)
					{
						socket->L = lua_newthread(ls); // new Lua thread for this socket
						socket->L_refid = lua_ref(ls, -1); // mkake a registry reference id for the thread to avoid garbage collection
						lua_pop(ls, 1); // pop the new Lua Thread

						// event refds
						socket->onmessage_refid = onmessage_refid;
						socket->onclose_refid = onclose_refid;
						socket->onerr_ref = onerr_ref;

						void* userdata = lua_newuserdatatagged(ls, sizeof(lua_websocket), 69);
						lua_newtable(ls);
						{

							lua_pushstring(ls, ("WebSocket"));
							lua_setfield(ls, -2, ("__type"));

							lua_pushcclosure(ls, websocket_index, nullptr, 0);
							lua_setfield(ls, -2, ("__index"));
						}
						lua_setmetatable(ls, -2);

						socket_map.insert({ userdata, socket });
						return 1;
					});
				});

		};
	}

	namespace Input {

		auto get_proc_id(const char* name) -> int {
			PROCESSENTRY32 entry;
			entry.dwSize = sizeof(PROCESSENTRY32);

			HANDLE snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, NULL);

			if (Process32First(snapshot, &entry) == TRUE)
			{
				while (Process32Next(snapshot, &entry) == TRUE)
				{
					if (_stricmp(entry.szExeFile, name) == 0)
					{
						CloseHandle(snapshot);
						return entry.th32ProcessID;
					}
				}
			}

			CloseHandle(snapshot);
			return 0;
		}

		__forceinline auto roblox_active() -> bool {
			int proc_id = get_proc_id("RobloxPlayerBeta.exe");
			HWND foreground = GetForegroundWindow();

			DWORD fproc_id;
			GetWindowThreadProcessId(foreground, &fproc_id);

			return (fproc_id == proc_id);
		}

		int isrbxactive(lua_State* rl)
		{
			HWND window;
			window = FindWindowA(NULL, "Roblox");
			lua_pushboolean(rl, GetForegroundWindow() == window);
			return 1;
		}

		__forceinline auto keypress(lua_State* L) -> int {
			L, 1, 1, luaL_checktype(L, 1, LUA_TNUMBER);
			UINT key = lua_tointeger(L, 1);

			if (roblox_active())
				keybd_event(0, (BYTE)MapVirtualKeyA(key, MAPVK_VK_TO_VSC), KEYEVENTF_SCANCODE, 0);

			return 0;
		}

		std::int32_t keytap(lua_State* L) {
			L, 1, 1, luaL_checktype(L, 1, LUA_TNUMBER);
			UINT key = lua_tointeger(L, 1);

			if (!roblox_active())
				return 0;

			keybd_event(0, MapVirtualKeyA(key, MAPVK_VK_TO_VSC), KEYEVENTF_SCANCODE, 0);
			keybd_event(0, MapVirtualKeyA(key, MAPVK_VK_TO_VSC), KEYEVENTF_SCANCODE | KEYEVENTF_KEYUP, 0);

			return 0;
		};

		__forceinline auto keyrelease(lua_State* L) -> int {
			luaL_checktype(L, 1, LUA_TNUMBER);
			UINT key = lua_tointeger(L, 1);

			if (roblox_active())
				keybd_event(0, (BYTE)MapVirtualKeyA(key, MAPVK_VK_TO_VSC), KEYEVENTF_SCANCODE | KEYEVENTF_KEYUP, 0);

			return 0;
		}

		__forceinline auto mouse1click(lua_State* L) -> int {
			if (roblox_active())
				mouse_event(MOUSEEVENTF_LEFTDOWN | MOUSEEVENTF_LEFTUP, 0, 0, 0, 0);

			return 0;
		}

		__forceinline auto mouse1press(lua_State* L) -> int {

			if (roblox_active())
				mouse_event(MOUSEEVENTF_LEFTDOWN, 0, 0, 0, 0);

			return 0;
		}

		__forceinline auto mouse1release(lua_State* L) -> int {

			if (roblox_active())
				mouse_event(MOUSEEVENTF_LEFTUP, 0, 0, 0, 0);

			return 0;
		}

		__forceinline auto mouse2click(lua_State* L) -> int {

			if (roblox_active())
				mouse_event(MOUSEEVENTF_RIGHTDOWN | MOUSEEVENTF_RIGHTUP, 0, 0, 0, 0);

			return 0;
		}

		__forceinline auto mouse2press(lua_State* L)
		{
			if (roblox_active())
				mouse_event(MOUSEEVENTF_RIGHTDOWN, 0, 0, 0, 0);

			return 0;
		}

		__forceinline auto mouse2release(lua_State* L) -> int {

			if (roblox_active())
				mouse_event(MOUSEEVENTF_RIGHTUP, 0, 0, 0, 0);

			return 0;
		}

		__forceinline auto mousemoveabs(lua_State* L) -> int {
			luaL_checktype(L, 1, LUA_TNUMBER);
			luaL_checktype(L, 2, LUA_TNUMBER);

			int x = lua_tointeger(L, 1);
			int y = lua_tointeger(L, 2);

			if (!roblox_active())
				return 0;

			int width = GetSystemMetrics(SM_CXSCREEN) - 1;
			int height = GetSystemMetrics(SM_CYSCREEN) - 1;

			RECT CRect;
			GetClientRect(GetForegroundWindow(), &CRect);

			POINT Point{ CRect.left, CRect.top };
			ClientToScreen(GetForegroundWindow(), &Point);

			x = (x + Point.x) * (65535 / width);
			y = (y + Point.y) * (65535 / height);

			mouse_event(MOUSEEVENTF_ABSOLUTE | MOUSEEVENTF_MOVE, x, y, 0, 0);
			return 0;
		}

		__forceinline auto mousemoverel(lua_State* L) -> int {
			luaL_checktype(L, 1, LUA_TNUMBER);
			luaL_checktype(L, 2, LUA_TNUMBER);

			int x = lua_tointeger(L, 1);
			int y = lua_tointeger(L, 2);

			if (roblox_active())
				mouse_event(MOUSEEVENTF_MOVE, x, y, 0, 0);

			return 0;
		}

		__forceinline auto mousescroll(lua_State* L) -> int {
			luaL_checktype(L, 1, LUA_TNUMBER);

			int amt = lua_tointeger(L, 1);

			if (roblox_active())
				mouse_event(MOUSEEVENTF_WHEEL, 0, 0, amt, 0);

			return 0;
		}

	}

	namespace Filesystem {
		namespace fs = std::filesystem;

		std::filesystem::path workspaceDir;
		std::filesystem::path assetsDir;

		namespace HelpFunctions {

			std::unordered_set<std::string> blacklistedExtensions = { ".csh", ".wsh", ".dll", ".bat", ".cmd", ".scr", ".vbs", ".js",
																	 ".ts",  ".wsf", ".msi", ".com", ".lnk", ".ps1", ".py", "vb", ".vbe",
																	 ".py3", ".pyc", ".pyw", ".vb", ".html", ".ws", ".psy", ".hta",
			};

			bool IsExtensionBlacklisted(const fs::path& path) {
				const auto extension = path.extension().string();
				return blacklistedExtensions.find(extension) != blacklistedExtensions.end();
			}

			bool IsPathSafe(const std::string& relativePath) {
				const fs::path base = fs::absolute(workspaceDir);
				const fs::path combined = base / relativePath;

				const fs::path normalizedBase = base.lexically_normal();
				const fs::path normalizedCombined = combined.lexically_normal();

				const auto baseStr = normalizedBase.string();
				const auto combinedStr = normalizedCombined.string();

				if (combinedStr.compare(0, baseStr.length(), baseStr) != 0)
					return false;

				std::string lowerRelativePath = relativePath;
				std::ranges::transform(lowerRelativePath, lowerRelativePath.begin(), ::tolower);

				if (lowerRelativePath.find("..") != std::string::npos)
					return false;

				if (IsExtensionBlacklisted(combined)) {
					return false;
				}

				return true;
			}

			__forceinline std::filesystem::path CheckPath(lua_State* L) {
				const auto relativePath = lua_tostring(L, 1);

				if (!IsPathSafe(relativePath))
					luaG_runerror(L, "You cannot escape the workspace directory or create blacklisted file types");

				return workspaceDir / relativePath;
			}

			void Init() {

				wchar_t Path[MAX_PATH];
				wchar_t Path2[MAX_PATH];

				static HMODULE module = ModuleDLL;

				GetModuleFileNameW(module, Path, MAX_PATH);
				const auto currentDirectory = fs::path(std::wstring(Path)).parent_path();

				workspaceDir = currentDirectory / "workspace";

				GetModuleFileNameW(GetModuleHandle(NULL), Path2, MAX_PATH);

				std::filesystem::path fullPath(Path2);
				std::filesystem::path contentDir = fullPath.parent_path() / "content";
				if (!std::filesystem::exists(contentDir)) {
					std::filesystem::create_directory(contentDir);
				}
				std::filesystem::path gcaDir = contentDir / "Env";
				if (!std::filesystem::exists(gcaDir)) {
					std::filesystem::create_directory(gcaDir);
				}

				std::wstring gcaPath = gcaDir.wstring();
				assetsDir = gcaDir;

			}

		}

		int readfile(lua_State* L) {


			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			if (!fs::exists(absolutePath) || !fs::is_regular_file(absolutePath)) {
				luaG_runerror(L, "File does not exist!");
			}

			std::ifstream file(absolutePath, std::ios::binary | std::ios::ate);
			if (!file.is_open()) {
				luaG_runerror(L, "Could not read the file content!");
			}

			std::streamsize size = file.tellg();
			file.seekg(0, std::ios::beg);
			std::vector<char> buffer(size);
			if (!file.read(buffer.data(), size)) {
				luaG_runerror(L, "Could not read the file content!");
			}

			lua_pushlstring(L, buffer.data(), size);

			return 1;
		}

		int listfiles(lua_State* L) {


			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			if (!fs::exists(absolutePath) || !fs::is_directory(absolutePath)) {
				luaG_runerror(L, "Folder does not exist!");
			}

			lua_newtable(L);
			int currentIndex = 1;
			for (const auto& entry : fs::directory_iterator(absolutePath)) {
				lua_pushstring(L, entry.path().string().c_str());
				lua_rawseti(L, -2, currentIndex);
				currentIndex++;
			}

			return 1;
		}

		int writefile(lua_State* L) {


			luaL_checkstring(L, 1);
			luaL_checkstring(L, 2);

			auto absolutePath = HelpFunctions::CheckPath(L);
			size_t contentLength;
			auto fileContent = lua_tolstring(L, 2, &contentLength);

			if (fs::is_directory(absolutePath)) {
				luaG_runerror(L, "Argument #1 is not a valid file!");
			}

			fs::create_directories(absolutePath.parent_path());

			std::ofstream file(absolutePath, std::ios::binary | std::ios::beg);
			if (!file.is_open()) {
				luaG_runerror(L, "Could not open the file!");
			}

			file.write(fileContent, contentLength);
			if (file.fail()) {
				luaG_runerror(L, "Cannot write content to the file!");
			}

			file.close();
			if (file.fail()) {
				luaG_runerror(L, "The attempt to close the file failed!");
			}

			return 0;
		}
		int appendfile(lua_State* L) {
			luaL_checktype(L, 1, LUA_TSTRING);
			luaL_checktype(L, 2, LUA_TSTRING);

			size_t contentSize = 0;
			std::string Path = luaL_checklstring(L, 1, 0);
			std::filesystem::path absolutePath = HelpFunctions::CheckPath(L);

			if (!fs::exists(absolutePath) || !fs::is_regular_file(absolutePath)) {
				luaG_runerror(L, "File does not exist!");
			}
			const auto Content = luaL_checklstring(L, 2, &contentSize);

			std::string absolutePathStr = absolutePath.string();

			std::replace(Path.begin(), Path.end(), '\\', '/');
			std::replace(absolutePathStr.begin(), absolutePathStr.end(), '\\', '/');

			std::ofstream fileToWrite(absolutePathStr, std::ios::binary | std::ios::app);
			fileToWrite << Content;
			fileToWrite.close();

			return 0;
		}

		int makefolder(lua_State* L) {
			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			if (fs::is_directory(absolutePath)) {
				return 0;
			}

			if (fs::is_regular_file(absolutePath)) {
				luaG_runerror(L, "There is a file on this path!");
			}

			if (fs::exists(absolutePath)) {
				luaG_runerror(L, "There is already something on this path!");
			}

			fs::create_directories(absolutePath);
			return 0;
		}

		int isfile(lua_State* L) {


			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			lua_pushboolean(L, fs::exists(absolutePath) && fs::is_regular_file(absolutePath));
			return 1;
		}

		int isfolder(lua_State* L) {


			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			lua_pushboolean(L, fs::exists(absolutePath) && fs::is_directory(absolutePath));
			return 1;
		}

		int delfile(lua_State* L) {


			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			if (!fs::exists(absolutePath) || !fs::is_regular_file(absolutePath)) {
				luaG_runerror(L, "File does not exist!");
			}

			fs::remove(absolutePath);
			return 0;
		}

		int delfolder(lua_State* L) {


			luaL_checkstring(L, 1);

			auto absolutePath = HelpFunctions::CheckPath(L);

			if (!fs::exists(absolutePath) || !fs::is_directory(absolutePath)) {
				luaG_runerror(L, "Folder does not exist!");
			}

			fs::remove_all(absolutePath);
			return 0;
		}

		int loadfile(lua_State* L) {


			luaL_checkstring(L, 1);

			auto relativePath = lua_tostring(L, 1);
			auto absolutePath = HelpFunctions::CheckPath(L);
			const char* sectionName = "";
			if (!lua_isnil(L, 2)) {
				sectionName = lua_tostring(L, 2);
			}

			if (!fs::exists(absolutePath) || !fs::is_regular_file(absolutePath)) {
				luaG_runerror(L, "File does not exist!");
			}

			auto close_file = [](FILE* f) { fclose(f); };
			auto holder = std::unique_ptr<FILE, decltype(close_file)>(fopen(absolutePath.string().c_str(), "rb"), close_file);

			if (!holder)
				return 0;

			FILE* f = holder.get();

			if (fseek(f, 0, SEEK_END) < 0)
				return 0;

			const long size = ftell(f);

			if (size < 0)
				return 0;

			if (fseek(f, 0, SEEK_SET) < 0)
				return 0;

			std::string res{};
			res.resize(size);
			fread(const_cast<char*>(res.data()), 1, size, f);

			return Execution::Lua_LoadString(L, res, "=Env");
		}

		int getcustomasset(lua_State* L) {


			luaL_checktype(L, 1, LUA_TSTRING);

			std::string assetname = lua_tostring(L, 1);
			std::filesystem::path workspace_path = workspaceDir / assetname;
			std::filesystem::path asset_directory = assetsDir / workspace_path.filename();

			std::filesystem::copy_file(workspace_path, asset_directory, std::filesystem::copy_options::update_existing);
			lua_pushstring(L, std::string("rbxasset://Env/" + asset_directory.filename().string()).data());
			return 1;
		}

	}

	namespace Cache {

		int invalidate(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);

			const auto rawUserdata = *static_cast<void**>(lua_touserdata(L, 1));

			lua_pushlightuserdata(L, (void*)rcv::PushInstance);
			lua_gettable(L, LUA_REGISTRYINDEX);

			lua_pushlightuserdata(L, reinterpret_cast<void*>(rawUserdata));
			lua_pushnil(L);
			lua_settable(L, -3);

			return 0;
		}

		int replace(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TUSERDATA);

			const auto rawUserdata = *static_cast<void**>(lua_touserdata(L, 1));

			lua_pushlightuserdata(L, (void*)rcv::PushInstance);
			lua_gettable(L, LUA_REGISTRYINDEX);

			lua_pushlightuserdata(L, rawUserdata);
			lua_pushvalue(L, 2);
			lua_settable(L, -3);

			return 0;
		}

		int iscached(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);

			const auto rawUserdata = *static_cast<void**>(lua_touserdata(L, 1));

			lua_pushlightuserdata(L, (void*)rcv::PushInstance);
			lua_gettable(L, LUA_REGISTRYINDEX);

			lua_pushlightuserdata(L, rawUserdata);
			lua_gettable(L, -2);

			lua_pushboolean(L, lua_type(L, -1) != LUA_TNIL);
			return 1;
		}

		int cloneref(lua_State* L)
		{
			auto Ud = lua_touserdata(L, 1);
			auto RawUd = *static_cast<void**>(Ud);

			lua_pushlightuserdata(L, reinterpret_cast<void*>(rcv::PushInstance)); // Roblox uses the pushinstance address for the globals list

			lua_rawget(L, LUA_REGISTRYINDEX);
			lua_pushlightuserdata(L, RawUd); // Let's check if the value exists in the registry
			lua_rawget(L, -2); // Grab the reg

			lua_pushlightuserdata(L, RawUd);
			lua_pushnil(L); // If the value exists, we need to set the ref to nil
			lua_rawset(L, -4);

			reinterpret_cast<void(__fastcall*)(lua_State*, void*)>(rcv::PushInstance)(L, Ud);
			// Now once we are done, we need to restore the instance
			lua_pushlightuserdata(L, RawUd);
			lua_pushvalue(L, -3);
			lua_rawset(L, -5);

			return 1;
		}

		int compareinstances(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TUSERDATA);

			uintptr_t instance_one = *reinterpret_cast<uintptr_t*>(lua_touserdata(L, 1));
			uintptr_t instance_two = *reinterpret_cast<uintptr_t*>(lua_touserdata(L, 2));

			lua_pushboolean(L, instance_one == instance_two);
			return 1;
		}

	}

	namespace Metatable
	{
		int getrawmetatable(lua_State* L) {
			luaL_checkany(L, 1);

			if (!lua_getmetatable(L, 1))
				lua_pushnil(L);
			else {
				lua_getmetatable(L, 1);
			}

			return 1;
		}

		int setrawmetatable(lua_State* L) {
			luaL_stackcheck(L, 2, 2);
			int t1 = lua_type(L, 1);
			if (t1 != LUA_TTABLE && t1 != LUA_TUSERDATA) {
				luaL_typeerror(L, 1, "Table or Userdata expected.");
				return 0;
			}

			int t2 = lua_type(L, 2);
			if (t2 != LUA_TTABLE && t2 != LUA_TNIL) {
				luaL_typeerror(L, 2, "Nil or Table");
				return 0;
			}

			lua_settop(L, 2);
			lua_pushboolean(L, lua_setmetatable(L, 1));
			lua_pushvalue(L, 1);

			return 1;
		}

		auto isreadonly(lua_State* L) -> int
		{
			luaL_stackcheck(L, 1, 1, checkType(L, 1, LUA_TTABLE));

			Table* t = (Table*)lua_topointer(L, 1);
			lua_pushboolean(L, t->readonly);

			return 1;
		}

		auto getnamecallmethod(lua_State* L) -> int
		{
			const auto szNamecall = lua_namecallatom(L, nullptr);

			if (szNamecall == nullptr)
				lua_pushnil(L);
			else
				lua_pushstring(L, szNamecall);

			return 1;
		}

		auto setnamecallmethod(lua_State* L) -> int
		{
			luaL_stackcheck(L, 1, 1, checkType(L, 1, LUA_TSTRING));
			L->namecall = tsvalue(luaA_toobject(L, 1));
			return 0;
		}


		auto setreadonly(lua_State* L) -> int
		{
			luaL_stackcheck(L, 2, 2, checkType(L, 1, LUA_TTABLE));
			luaL_checktype(L, 2, LUA_TBOOLEAN);

			lua_setreadonly(L, 1, lua_toboolean(L, 2));
			return 0;
		}


		auto make_writable(lua_State* rl) -> int
		{
			lua_setreadonly(rl, 1, false);
			return 0;
		}


		auto make_readonly(lua_State* rl) -> int
		{
			lua_setreadonly(rl, 1, true);
			return 0;
		}
	}

	namespace Crypt {

		enum CryptModes
		{
			//AES
			AES_CBC,
			AES_CFB,
			AES_CTR,
			AES_OFB,
			AES_GCM,
			AES_EAX,

			//Blowfish
			BF_CBC,
			BF_CFB,
			BF_OFB
		};

		enum HashModes
		{
			//MD5
			MD5,

			//SHA1
			SHA1,

			//SHA2
			SHA224,
			SHA256,
			SHA384,
			SHA512,

			//SHA3
			SHA3_224,
			SHA3_256,
			SHA3_384,
			SHA3_512,
		};

		std::map<std::string, CryptModes> CryptTranslationMap = {
			//AES
			{ "aes-cbc", AES_CBC },
			{ "aes_cbc", AES_CBC },

			{ "aes-cfb", AES_CFB },
			{ "aes_cfb", AES_CFB },

			{ "aes-ctr", AES_CTR },
			{ "aes_ctr", AES_CTR },

			{ "aes-ofb", AES_OFB },
			{ "aes_ofb", AES_OFB },

			{ "aes-gcm", AES_GCM },
			{ "aes_gcm", AES_GCM },

			{ "aes-eax", AES_EAX },
			{ "aes_eax", AES_EAX },

			//Blowfish
			{ "blowfish-cbc", BF_CBC },
			{ "blowfish_cbc", BF_CBC },
			{ "bf-cbc", BF_CBC },
			{ "bf_cbc", BF_CBC },

			{ "blowfish-cfb", BF_CFB },
			{ "blowfish_cfb", BF_CFB },
			{ "bf-cfb", BF_CFB },
			{ "bf_cfb", BF_CFB },

			{ "blowfish-ofb", BF_OFB },
			{ "blowfish_ofb", BF_OFB },
			{ "bf-ofb", BF_OFB },
			{ "bf_ofb", BF_OFB },
		};

		std::map<std::string, HashModes> HashTranslationMap = {
			//MD5
			{ "md5", MD5 },

			//SHA1
			{ "sha1", SHA1 },

			//SHA2
			{ "sha224", SHA224 },
			{ "sha256", SHA256 },
			{ "sha384", SHA384 },
			{ "sha512", SHA512 },

			//SHA3
			{ "sha3-224", SHA3_224 },
			{ "sha3_224", SHA3_224 },
			{ "sha3-256", SHA3_256 },
			{ "sha3_256", SHA3_256 },
			{ "sha3-384", SHA3_384 },
			{ "sha3_384", SHA3_384 },
			{ "sha3-512", SHA3_512 },
			{ "sha3_512", SHA3_512 },
		};

		namespace HelpFunctions {

			std::string Base64Decode(const std::string& encoded_string)
			{
				std::string decoded;
				CryptoPP::StringSource ss(encoded_string, true,
					new CryptoPP::Base64Decoder(
						new CryptoPP::StringSink(decoded)
					));

				return decoded;
			}

			std::string Base64Encode(const byte* bytes_to_encode, size_t in_len)
			{
				std::string encoded;
				CryptoPP::StringSource ss(bytes_to_encode, in_len, true,
					new CryptoPP::Base64Encoder(
						new CryptoPP::StringSink(encoded),
						false
					));

				return encoded;
			}

			template<typename T>
			static __forceinline std::string hash_with_algo(const std::string& Input)
			{
				T Hash;
				std::string Digest;

				CryptoPP::StringSource SS(Input, true,
					new CryptoPP::HashFilter(Hash,
						new CryptoPP::HexEncoder(
							new CryptoPP::StringSink(Digest), false
						)));

				return Digest;
			}

			std::string random_string(int len) {
				static const char* chars = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZbcdefghijklmnopqrstuvwxyz";

				std::string str;
				str.reserve(len);

				for (int i = 0; i < len; ++i) {
					str += chars[rand() % (strlen(chars) - 1)];
				}

				return str;
			}

			void SplitString(std::string Str, std::string By, std::vector<std::string>& Tokens)
			{
				Tokens.push_back(Str);
				const auto splitLen = By.size();
				while (true)
				{
					auto frag = Tokens.back();
					const auto splitAt = frag.find(By);
					if (splitAt == std::string::npos)
						break;
					Tokens.back() = frag.substr(0, splitAt);
					Tokens.push_back(frag.substr(splitAt + splitLen, frag.size() - (splitAt + splitLen)));
				}
			}

			template<typename T>
			__forceinline std::string DecryptAuthenticatedWithAlgo(lua_State* L, const std::string& Ciphertext, const std::string& Key, const std::string& IV)
			{
				try
				{
					std::string Decrypted;

					T Decryptor;
					Decryptor.SetKeyWithIV((byte*)Key.c_str(), Key.size(), (byte*)IV.c_str(), IV.size());

					const auto Base = Base64Decode(Ciphertext);

					CryptoPP::AuthenticatedDecryptionFilter Adf(Decryptor,
						new CryptoPP::StringSink(Decrypted)
					);

					Adf.Put((const byte*)Base.data(), Base.size());
					Adf.MessageEnd();

					return Decrypted;
				}
				catch (CryptoPP::Exception& e)
				{
					luaL_error(L, e.what());
					return "";
				}
			}

			template<typename T>
			__forceinline std::string EncryptAuthenticatedWithAlgo(lua_State* L, const std::string& data, const std::string& key_size, const std::string& ivc_str)
			{
				try
				{
					std::string Encrypted;

					T Encryptor;
					Encryptor.SetKeyWithIV((byte*)key_size.c_str(), key_size.size(), (byte*)ivc_str.c_str(), ivc_str.size());

					CryptoPP::AuthenticatedEncryptionFilter Aef(Encryptor,
						new CryptoPP::StringSink(Encrypted)
					);

					Aef.Put((const byte*)data.data(), data.size());
					Aef.MessageEnd();

					return Base64Encode((unsigned char*)Encrypted.c_str(), Encrypted.size());
				}
				catch (CryptoPP::Exception& e)
				{
					luaL_error(L, e.what());
					return "";
				}
			}

		}

		int encrypt(lua_State* L) {
			luaL_stackcheck(L, 2, 2);
			std::string data = luaL_checklstring(L, 1, NULL);
			std::string key = luaL_checklstring(L, 2, NULL);

			CryptoPP::AutoSeededRandomPool Prng;
			byte IV[12];
			Prng.GenerateBlock(IV, 12);

			byte derived_key[32];
			CryptoPP::PKCS5_PBKDF2_HMAC<CryptoPP::SHA384> KDF;
			KDF.DeriveKey(derived_key, 32, 0, (byte*)key.c_str(), key.size(), NULL, 0, 10000);

			auto encrypted = HelpFunctions::EncryptAuthenticatedWithAlgo<CryptoPP::GCM<CryptoPP::AES>::Encryption>(L,
				std::string(data.c_str(), data.size()),
				std::string((const char*)derived_key, 32),
				std::string((const char*)IV, 12));

			encrypted += "|" + HelpFunctions::Base64Encode(IV, 12);
			encrypted = HelpFunctions::Base64Encode((byte*)encrypted.data(), encrypted.size());


			lua_pushlstring(L, encrypted.c_str(), encrypted.size());
			lua_pushlstring(L, reinterpret_cast<const char*>(IV), sizeof(IV));
			return 2;
		}

		int decrypt(lua_State* L) {
			luaL_stackcheck(L, 2, 2);
			std::string data = luaL_checklstring(L, 1, NULL);
			std::string key = luaL_checklstring(L, 2, NULL);

			byte DerivedKey[32];
			CryptoPP::PKCS5_PBKDF2_HMAC<CryptoPP::SHA384> KDF;
			KDF.DeriveKey(DerivedKey, 32, 0, (byte*)key.c_str(), key.size(), NULL, 0, 10000);

			std::vector<std::string> Split;
			HelpFunctions::SplitString(HelpFunctions::Base64Decode(data), "|", Split);

			if (Split.size() != 2) {
				luaL_argerror(L, 1, "Invalid encrypted string specified");
				return 0;
			}

			auto decrypted = HelpFunctions::DecryptAuthenticatedWithAlgo<CryptoPP::GCM<CryptoPP::AES>::Decryption>(L,
				Split.at(0),
				std::string((const char*)DerivedKey, 32),
				HelpFunctions::Base64Decode(Split.at(1)));


			lua_pushlstring(L, decrypted.c_str(), decrypted.size());
			return 1;
		}

		int generatebytes(lua_State* L) {
			luaL_stackcheck(L, 1, 1);
			int len = luaL_checkinteger(L, 1);

			if (len > 1024)
			{
				luaL_argerror(L, 1, "Exceeded maximum size (1024)");
				return 0;
			}

			if (len < 0)
			{
				luaL_argerror(L, 1, "Negative size specified");
				return 0;
			}

			std::string data = HelpFunctions::random_string(len);

			auto encoded = HelpFunctions::Base64Encode((unsigned char*)data.c_str(), data.size());
			lua_pushlstring(L, encoded.c_str(), encoded.size());

			return 1;
		}

		int generatekey(lua_State* L) {
			luaL_stackcheck(L, 0, 0);
			std::string data = HelpFunctions::random_string(32);

			auto encoded = HelpFunctions::Base64Encode((unsigned char*)data.c_str(), data.size());
			lua_pushlstring(L, encoded.c_str(), encoded.size());

			return 1;
		}

		int hash(lua_State* L) {
			luaL_stackcheck(L, 2, 2);
			std::string algo = luaL_checklstring(L, 2, NULL);
			std::string data = luaL_checklstring(L, 1, NULL);

			std::transform(algo.begin(), algo.end(), algo.begin(), tolower);

			if (!HashTranslationMap.count(algo))
			{

				luaL_argerror(L, 1, "Non-existant hash algorithm");
				return 0;
			}

			const auto ralgo = HashTranslationMap[algo];

			std::string hash;

			if (ralgo == MD5) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::MD5>(data);
			}
			else if (ralgo == SHA1) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA1>(data);
			}
			else if (ralgo == SHA224) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA224>(data);
			}
			else if (ralgo == SHA256) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA256>(data);
			}
			else if (ralgo == SHA384) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA384>(data);
			}
			else if (ralgo == SHA512) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA512>(data);
			}
			else if (ralgo == SHA3_224) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA3_224>(data);
			}
			else if (ralgo == SHA3_256) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA3_256>(data);
			}
			else if (ralgo == SHA3_384) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA3_384>(data);
			}
			else if (ralgo == SHA3_512) {
				hash = HelpFunctions::hash_with_algo<CryptoPP::SHA3_512>(data);
			}
			else {

				luaL_argerror(L, 1, "non-existant hash algorithm");
				return 0;
			}

			lua_pushlstring(L, hash.c_str(), hash.size());

			return 1;
		}

		int base64encode(lua_State* L) {
			luaL_stackcheck(L, 1, 1);
			std::string data = luaL_checklstring(L, 1, NULL);

			auto encoded = HelpFunctions::Base64Encode((unsigned char*)data.c_str(), data.size());
			lua_pushlstring(L, encoded.c_str(), encoded.size());

			return 1;
		}

		int base64decode(lua_State* L) {
			luaL_stackcheck(L, 1, 1);
			const auto data = luaL_checklstring(L, 1, NULL);

			auto decoded = HelpFunctions::Base64Decode(data);

			lua_pushlstring(L, decoded.c_str(), decoded.size());

			return 1;
		}

	}

	namespace HTTP {

		int httpget(lua_State* L) {


			std::string url;

			if (!lua_isstring(L, 1)) {
				luaL_checkstring(L, 2);
				url = std::string(lua_tostring(L, 2));
			}
			else {
				url = std::string(lua_tostring(L, 1));
			}

			if (url.find("http://") == std::string::npos && url.find("https://") == std::string::npos) {
				luaL_argerror(L, 1, "Invalid protocol (expected 'http://' or 'https://')");
			}

			return Scheduler::YieldExecution(L, [url]() -> std::function<int(lua_State*)> {
				cpr::Header Headers;
				std::optional<std::string> job_id = r_get_jobid();
				using json = nlohmann::json;
				json sessionIdJson;

				if (job_id.has_value()) {
					sessionIdJson["GameId"] = job_id.value();
					sessionIdJson["PlaceId"] = job_id.value();
					Headers.insert({ "Roblox-Game-Id", job_id.value() });
				}
				else {
					sessionIdJson["GameId"] = "empty value";
					sessionIdJson["PlaceId"] = "empty value";
					Headers.insert({ "Roblox-Game-Id", "empty value" });
				}

				Headers.insert({ "User-Agent", "Roblox/WinInet" });
				Headers.insert({ "Roblox-Session-Id", sessionIdJson.dump() });
				Headers.insert({ "Accept-Encoding", "identity" });

				cpr::Response Result;
				try {
					Result = cpr::Get(cpr::Url{ url }, cpr::Header(Headers));
				}
				catch (const std::exception& e) {
					return [e](lua_State* L) -> int {
						lua_pushstring(L, ("HttpGet failed: " + std::string(e.what())).c_str());
						return 1;
						};
				}

				return [Result](lua_State* L) -> int {
					try {
						if (Result.status_code == 0 || HttpStatus::IsError(Result.status_code)) {
							auto Error = std::format("HttpGet failed with status {} - {}", Result.status_code, Result.error.message);

							lua_pushstring(L, Error.c_str());
							return 1;
						}

						if (Result.status_code == 401) {
							lua_pushstring(L, "HttpGet failed with unauthorized access");
							return 1;
						}

						lua_pushlstring(L, Result.text.data(), Result.text.size());


						return 1;

					}
					catch (const std::exception& e) {

						lua_pushstring(L, "HttpGet failed");
						return 1;
					}
					catch (...) {
						lua_pushstring(L, "HttpGet failed");
						return 1;
					}
					};
				});
		}

		int request(lua_State* L) {


			luaL_checktype(L, 1, LUA_TTABLE);

			lua_getfield(L, 1, "Url");
			if (lua_type(L, -1) != LUA_TSTRING) {
				luaL_error(L, "Invalid or no 'Url' field specified in request table");
				return 0;
			}

			std::string Url = lua_tostring(L, -1);
			if (Url.find("http") != 0) {
				luaL_error(L, "Invalid protocol specified (expected 'http://' or 'https://')");
				return 0;
			}

			lua_pop(L, 1);

			auto Method = H_GET;
			lua_getfield(L, 1, "Method");

			if (lua_type(L, -1) == LUA_TSTRING) {
				std::string Methods = luaL_checkstring(L, -1);
				std::transform(Methods.begin(), Methods.end(), Methods.begin(), tolower);

				if (!RequestMethodMap.count(Methods)) {
					luaL_error(L, "request type '%s' is not a valid http request type.", Methods.c_str());
					return 0;
				}

				Method = RequestMethodMap[Methods];
			}

			lua_pop(L, 1);

			cpr::Header Headers;

			lua_getfield(L, 1, "Headers");
			if (lua_type(L, -1) == LUA_TTABLE) {
				lua_pushnil(L);

				while (lua_next(L, -2)) {
					if (lua_type(L, -2) != LUA_TSTRING || lua_type(L, -1) != LUA_TSTRING) {
						luaL_error(L, "'Headers' table must contain string keys/values.");
						return 0;
					}

					std::string HeaderKey = luaL_checkstring(L, -2);
					auto HeaderCopy = std::string(HeaderKey);
					std::ranges::transform(HeaderKey, HeaderKey.begin(), tolower);

					if (HeaderCopy == "content-length") {
						luaL_error(L, "Headers: 'Content-Length' header cannot be overwritten.");
						return 0;
					}

					std::string HeaderValue = luaL_checkstring(L, -1);
					Headers.insert({ HeaderKey, HeaderValue });
					lua_pop(L, 1);
				}
			}
			lua_pop(L, 1);

			cpr::Cookies Cookies;
			lua_getfield(L, 1, "Cookies");

			if (lua_type(L, -1) == LUA_TTABLE) {
				std::map<std::string, std::string> RobloxCookies;
				lua_pushnil(L);

				while (lua_next(L, -2)) {
					if (lua_type(L, -2) != LUA_TSTRING || lua_type(L, -1) != LUA_TSTRING) {
						luaL_error(L, "'Cookies' table must contain string keys/values.");
						return 0;
					}

					std::string CookieKey = luaL_checkstring(L, -2);
					std::string CookieValue = luaL_checkstring(L, -1);

					RobloxCookies[CookieKey] = CookieValue;
					lua_pop(L, 1);
				}

				Cookies = RobloxCookies;
			}

			lua_pop(L, 1);

			auto HasUserAgent = false;
			for (auto& Header : Headers) {
				auto HeaderName = Header.first;
				std::transform(HeaderName.begin(), HeaderName.end(), HeaderName.begin(), tolower);

				if (HeaderName == "user-agent")
					HasUserAgent = true;
			}

			if (!HasUserAgent) {
				Headers.insert({ "User-Agent", ("Env") });
			}

			auto hwidd = GetHwid();

			if (hwidd.has_value()) {
				Headers.insert({ ("Env-Fingerprint"), GetHwid().value() });
			}
			else {
				Headers.insert({ ("Env-Fingerprint"), "fe8451e8fbfcc55408f4253c31ff15085832f96ab266a6a041b9ddf8bb77a627" });
			}

			std::optional<std::string> job_id = r_get_jobid();
			std::optional<uintptr_t> place_id = r_get_placeid();

			if (job_id.has_value()) {

				Headers.insert({ "Roblox-Game-Id", job_id.value() });
			}
			else {
				Headers.insert({ "Roblox-Game-Id", "empty value" });
			}

			using json = nlohmann::json;
			json sessionIdJson;

			if (job_id.has_value()) {
				sessionIdJson["GameId"] = job_id.value();
				sessionIdJson["PlaceId"] = job_id.value();
			}
			else {
				sessionIdJson["GameId"] = "empty value";
				sessionIdJson["PlaceId"] = "empty value";
			}

			Headers.insert({ "Roblox-Session-Id", sessionIdJson.dump() });

			std::string Body;
			lua_getfield(L, 1, "Body");
			if (lua_type(L, -1) == LUA_TTABLE) {
				if (Method == H_GET || Method == H_HEAD) {
					luaL_error(L, "'Body' cant be represent in Get or head requests");
					return 0;
				}

				Body = luaL_checkstring(L, -1);
			}

			lua_pop(L, 1);

			return Scheduler::YieldExecution(L,
				[Method, Url, Headers, Cookies, Body]() -> auto {
					cpr::Response Response;

					switch (Method) {
					case H_GET: {
						Response = cpr::Get(cpr::Url{ Url }, Cookies, Headers);
						break;
					}
					case H_HEAD: {
						Response = cpr::Head(cpr::Url{ Url }, Cookies, Headers);
						break;
					}
					case H_POST: {
						Response = cpr::Post(cpr::Url{ Url }, cpr::Body{ Body }, Cookies, Headers);
						break;
					}
					case H_PUT: {
						Response = cpr::Put(cpr::Url{ Url }, cpr::Body{ Body }, Cookies, Headers);
						break;
					}
					case H_DELETE: {
						Response = cpr::Delete(cpr::Url{ Url }, cpr::Body{ Body }, Cookies, Headers);
						break;
					}
					case H_OPTIONS: {
						Response = cpr::Options(cpr::Url{ Url }, cpr::Body{ Body }, Cookies, Headers);
						break;
					}
					default: {
						throw std::exception("invalid request type");
					}
					}

					return [Response](lua_State* L) -> int {

						lua_newtable(L);

						lua_pushboolean(L, HttpStatus::IsSuccessful(Response.status_code));
						lua_setfield(L, -2, "Success");

						lua_pushinteger(L, Response.status_code);
						lua_setfield(L, -2, "StatusCode");

						auto Phrase = HttpStatus::ReasonPhrase(Response.status_code);
						lua_pushlstring(L, Phrase.c_str(), Phrase.size());
						lua_setfield(L, -2, "StatusMessage");

						lua_newtable(L);

						for (auto& Header : Response.header) {
							lua_pushlstring(L, Header.first.c_str(), Header.first.size());
							lua_pushlstring(L, Header.second.c_str(), Header.second.size());

							lua_settable(L, -3);
						}

						lua_setfield(L, -2, "Headers");

						lua_newtable(L);

						for (auto& cookie : Response.cookies.map_) {
							lua_pushlstring(L, cookie.first.c_str(), cookie.first.size());
							lua_pushlstring(L, cookie.second.c_str(), cookie.second.size());

							lua_settable(L, -3);
						}

						lua_setfield(L, -2, "Cookies");

						lua_pushlstring(L, Response.text.c_str(), Response.text.size());
						lua_setfield(L, -2, "Body");

						return 1;
						};
				}
			);

			//return 0;
		}

	}

	namespace Debug {
		auto debug_header_getclosure(lua_State* ls, bool allowCclosure = false, bool popcl = true) -> Closure*
		{
			luaL_checkany(ls, 1);

			if (!(lua_isfunction(ls, 1) || lua_isnumber(ls, 1)))
			{
				luaL_argerror(ls, 1, oxorany("Function or Number expected. expected."));
			}

			int level = 0;
			if (lua_isnumber(ls, 1))
			{
				level = lua_tointeger(ls, 1);

				if (level <= 0)
				{
					luaL_argerror(ls, 1, oxorany("Invalid stack level."));
				}
			}
			else if (lua_isfunction(ls, 1))
			{
				level = -lua_gettop(ls);
			}

			lua_Debug ar;
			if (!lua_getinfo(ls, level, "f", &ar))
			{
				luaL_argerror(ls, 1, oxorany("Invalid stack level."));
			}

			if (!lua_isfunction(ls, -1))
			{
				luaL_argerror(ls, 1, oxorany("This Stack is not pointing to a function."));
			}

			if (!allowCclosure && lua_iscfunction(ls, -1))
			{
				luaL_argerror(ls, 1, oxorany("Expected a Lua Closure!"));
			}

			auto closure = clvalue(luaA_toobject(ls, -1));
			if (popcl) lua_pop(ls, 1);

			return closure;
		}

		int debug_getconstants(lua_State* L) {
			luaL_checkany(L, 1);

			if (lua_iscfunction(L, -1))
			{
				luaL_argerror(L, 1, oxorany("Expected a Lua Closure!"));
			}

			if (lua_type(L, 1) != LUA_TNUMBER && lua_type(L, 1) != LUA_TFUNCTION)
				luaL_argerror(L, 1, "Expected <number> or <function>");

			if (lua_type(L, 1) == LUA_TNUMBER) {
				// TODO stack indexing
				lua_newtable(L);
				return 1;
			}

			const auto cl = clvalue(luaA_toobject(L, 1));

			lua_newtable(L);

			for (auto i = 0; i < cl->l.p->sizek; i++) {
				const auto constant = &cl->l.p->k[i];

				if (constant->tt == LUA_TTABLE || constant->tt == LUA_TNIL || constant->tt == LUA_TFUNCTION) {
					lua_pushnil(L);
					lua_rawseti(L, -2, i + 1);
					continue;
				}

				TValue* i_o = (L->top);
				i_o->value = constant->value;
				i_o->tt = constant->tt;
				incr_top(L);

				lua_rawseti(L, -2, i + 1);
			}

			return 1;
		}

		int debug_getconstant(lua_State* L) {
			luaL_checktype(L, 1, LUA_TFUNCTION);
			luaL_checktype(L, 2, LUA_TNUMBER);

			if (lua_iscfunction(L, 1)) {
				lua_pushnil(L);
				return 1;
			}

			int Idx = lua_tonumber(L, 2);
			Proto* p = clvalue(luaA_toobject(L, 1))->l.p;
			if (!p) {
				lua_pushnil(L);
				return 1;
			}

			if (Idx < 1 || Idx > p->sizek) {
				lua_pushnil(L);
				return 1;
			}

			TValue* KTable = p->k;
			if (!KTable) {
				lua_pushnil(L);
				return 1;
			}

			TValue* tval = &(KTable[Idx - 1]);
			if (!tval) {
				lua_pushnil(L);
				return 1;
			}

			if (tval->tt == LUA_TFUNCTION) {
				lua_pushnil(L);
				return 1;
			}

			TValue* i_o = (L->top);
			i_o->value = tval->value;
			i_o->tt = tval->tt;
			L->top++;

			return 1;
		}

		int debug_setconstant(lua_State* rl) {

			luaL_checktype(rl, 1, LUA_TFUNCTION);

			const auto closure = *reinterpret_cast<Closure**>(index2addr(rl, 1));

			if (!closure->isC) {
				const std::uint32_t index = lua_tonumber(rl, 2) - 1;
				const auto constant = &closure->l.p->k[index];

				setobj(rl, constant, index2addr(rl, 3));
			}

			return 0;
		}

		int debug_getupvalues(lua_State* L) {
			luaL_checktype(L, 1, LUA_TFUNCTION);

			if (lua_iscfunction(L, 1)) {
				//luaL_argerror(L, 1, "Lua function expected 4");
				lua_newtable(L);
				return 1;
			}

			Closure* cl = clvalue(luaA_toobject(L, 1));

			lua_newtable(L);

			for (int i = 0; i < cl->nupvalues; i++) {
				const char* upvalueName = lua_getupvalue(L, 1, i + 1);

				if (upvalueName) {
					const auto object = luaA_toobject(L, -1);
				}
				else
					lua_pushnil(L);
				lua_rawseti(L, -2, i + 1);
			}
			return 1;
		}

		int debug_getupvalue(lua_State* L) {
			luaL_checktype(L, 1, LUA_TFUNCTION);
			luaL_checktype(L, 2, LUA_TNUMBER);

			if (lua_iscfunction(L, 1)) {
				lua_pushnil(L);
				return 1;
			}

			int idx = lua_tonumber(L, 2);

			lua_getupvalue(L, 1, idx);
			return 1;
		}

		int debug_setupvalue(lua_State* L) {
			luaL_checktype(L, 1, LUA_TFUNCTION);
			luaL_checktype(L, 2, LUA_TNUMBER);

			if (lua_iscfunction(L, 1))
				return 0;

			int idx = lua_tonumber(L, 2);

			lua_setupvalue(L, 1, idx);
			return 0;
		}

		auto debug_helper_clone_proto(lua_State* ls, Proto* proto) -> Proto*
		{
			// Make a new proto.
			// We gotta make new GCObjects for the proto.
			Proto* clone = luaF_newproto(ls);

			// Copy constants
			clone->sizek = proto->sizek;
			clone->k = luaM_newarray(ls, proto->sizek, TValue, proto->memcat);
			for (int j = 0; j < proto->sizek; ++j)
			{
				clone->k[j].tt = proto->k[j].tt;
				clone->k[j].value = proto->k[j].value;
			}

			clone->lineinfo = 0;
			clone->locvars = 0;
			clone->nups = 0;
			clone->sizeupvalues = 0;
			clone->sizelineinfo = 0;
			clone->linegaplog2 = 0;
			clone->sizelocvars = 0;
			clone->linedefined = 0;

			// Copy debugname and source, make new TStrings
			if (proto->debugname)
			{
				const auto debugname = getstr(proto->debugname);
				const auto sz = strlen(debugname);

				clone->debugname = luaS_newlstr(ls, debugname, sz);
			}

			if (proto->source)
			{
				const auto source = getstr(proto->source);
				const auto sz = strlen(source);

				clone->source = luaS_newlstr(ls, source, sz);
			}

			clone->numparams = proto->numparams;
			clone->is_vararg = proto->is_vararg;
			clone->maxstacksize = proto->maxstacksize;
			clone->bytecodeid = proto->bytecodeid;

			// Set the code to return nothing.
			clone->sizecode = 1;
			clone->code = luaM_newarray(ls, clone->sizecode, Instruction, proto->memcat);
			clone->code[0] = 0x10082; // RETURN [ insn, enc 227 ]
			clone->codeentry = clone->code;
			clone->debuginsn = 0;

			// Copy protos
			clone->sizep = proto->sizep;
			clone->p = luaM_newarray(ls, proto->sizep, Proto*, proto->memcat);
			for (int j = 0; j < proto->sizep; ++j)
			{
				clone->p[j] = debug_helper_clone_proto(ls, proto->p[j]);
			}

			return clone;
		}

		static int debug_getprotos(lua_State* ls)
		{
			const auto closure = debug_header_getclosure(ls);
			const auto p = debug_helper_clone_proto(ls, closure->l.p); // Proto Clone

			// Create a table with space for the number of protos ( if any )
			lua_createtable(ls, p->sizep, 0);
			for (int i = 0; i < p->sizep; i++)
			{
				// Make a LClosure for them
				// We want to avoid vulns, hence the clones with empty code
				Proto* proto = p->p[i];
				Closure* pcl = luaF_newLclosure(ls, closure->nupvalues, closure->env, proto);

				luaC_threadbarrier(ls) setclvalue(ls, ls->top, pcl) ls->top++;

				lua_rawseti(ls, -2, i + 1);
			}

			return 1;
		}

		int debug_getproto(lua_State* L) {
			Closure* cl;
			if (lua_isnumber(L, 1)) {
				lua_Debug ar;
				if (!lua_getinfo(L, luaL_checkinteger(L, 1), "f", &ar))
					luaL_argerror(L, 1, "Level is out of range.");
				if (lua_iscfunction(L, -1))
					luaL_argerror(L, 1, "Level points to a CClosure");
				cl = (Closure*)lua_topointer(L, -1);
			}
			else if (lua_isfunction(L, 1)) {
				luaL_checktype(L, 1, LUA_TFUNCTION);
				cl = (Closure*)lua_topointer(L, 1);
				if (cl->isC)
					luaL_argerror(L, 1, "LuaClosure expected.");
			}
			else {
				luaL_argerror(L, 1, "Function or Number expected. expected.");
			}
			int index = luaL_checkinteger(L, 2);
			bool active = false;
			if (!lua_isnoneornil(L, 3))
				active = luaL_checkboolean(L, 3);
			if (!active) {
				if (index < 1 || index > cl->l.p->sizep)
					luaL_argerror(L, 2, "Index is out of range.");
				Proto* p = cl->l.p->p[index - 1];
				std::unique_ptr<TValue> function(new TValue{});
				setclvalue(L, function.get(), luaF_newLclosure(L, 0, cl->env, p));
				luaA_pushobject(L, function.get());
			}
			else {
				lua_newtable(L);

				struct Ctx {
					lua_State* L;
					int count;
					Closure* cl;
				} ctx{ L, 0, cl };

				luaM_visitgco(L, &ctx, [](void* pctx, lua_Page* page, GCObject* gco) -> bool {
					Ctx* ctx = static_cast<Ctx*>(pctx);
					if (!((gco->gch.marked ^ WHITEBITS) & otherwhite(ctx->L->global)))
						return false;

					uint8_t tt = gco->gch.tt;
					if (tt == LUA_TFUNCTION) {
						Closure* cl = (Closure*)gco;
						if (!cl->isC && cl->l.p == ctx->cl->l.p->p[ctx->count]) {
							setclvalue(ctx->L, ctx->L->top, cl);
							ctx->L->top++;
							lua_rawseti(ctx->L, -2, ++ctx->count);
						}
					}
					return false;
					});
			}
			return 1;
		}

		static int debug_getstack(lua_State* ls)
		{
			luaL_checkany(ls, 1);

			if (!(lua_isfunction(ls, 1) || lua_isnumber(ls, 1)))
			{
				luaL_argerror(ls, 1, ("function or number"));
			}

			int level = 0;
			if (lua_isnumber(ls, 1))
			{
				level = lua_tointeger(ls, 1);

				if (level <= 0)
				{
					luaL_argerror(ls, 1, ("invalid stack level."));
				}
			}
			else if (lua_isfunction(ls, 1))
			{
				level = -lua_gettop(ls);
			}

			lua_Debug ar;
			if (!lua_getinfo(ls, level, "f", &ar))
			{
				luaL_argerror(ls, 1, ("invalid stack level."));
			}

			if (!lua_isfunction(ls, -1))
			{
				luaL_argerror(ls, 1, ("stack does not point to a function."));
			}

			if (lua_iscfunction(ls, -1))
			{
				luaL_argerror(ls, 1, ("expected Lua Closure"));
			}

			lua_pop(ls, 1);

			auto ci = ls->ci[-level];

			if (lua_isnumber(ls, 2))
			{
				const auto idx = lua_tointeger(ls, 2) - 1;

				if (idx >= cast_int(ci.top - ci.base) || idx < 0)
				{
					luaL_argerror(ls, 2, ("Invalid stack index."));
				}

				auto val = ci.base + idx;
				luaC_threadbarrier(ls) luaA_pushobject(ls, val);
			}
			else
			{
				int idx = 0;
				lua_newtable(ls);

				for (auto val = ci.base; val < ci.top; val++)
				{
					lua_pushinteger(ls, idx++ + 1);

					luaC_threadbarrier(ls) luaA_pushobject(ls, val);

					lua_settable(ls, -3);
				}
			}

			return 1;
		}

		static int debug_setstack(lua_State* ls)
		{
			luaL_checkany(ls, 1);

			if (!(lua_isfunction(ls, 1) || lua_isnumber(ls, 1)))
			{
				luaL_argerror(ls, 1, ("function or number"));
			}

			int level = 0;
			if (lua_isnumber(ls, 1))
			{
				level = lua_tointeger(ls, 1);

				if (level <= 0)
				{
					luaL_argerror(ls, 1, ("invalid stack level."));
				}
			}
			else if (lua_isfunction(ls, 1))
			{
				level = -lua_gettop(ls);
			}

			lua_Debug ar;
			if (!lua_getinfo(ls, level, "f", &ar))
			{
				luaL_argerror(ls, 1, ("invalid stack level."));
			}

			if (!lua_isfunction(ls, -1))
			{
				luaL_argerror(ls, 1, ("stack does not point to a function."));
			}

			if (lua_iscfunction(ls, -1))
			{
				luaL_argerror(ls, 1, ("expected Lua Closure"));
			}

			lua_pop(ls, 1);

			luaL_checkany(ls, 3);

			auto ci = ls->ci[-level];

			const auto idx = luaL_checkinteger(ls, 2) - 1;
			if (idx >= cast_int(ci.top - ci.base) || idx < 0)
			{
				luaL_argerror(ls, 2, ("Invalid stack index."));
			}

			if ((ci.base + idx)->tt != luaA_toobject(ls, 3)->tt)
			{
				luaL_argerror(ls, 3, ("Source type does not match the Target type."));
			}

			setobj2s(ls, (ci.base + idx), luaA_toobject(ls, 3))
				return 0;
		}

		static int debug_getinfo(lua_State* ls)
		{
			luaL_checkany(ls, 1);

			if (!(lua_isfunction(ls, 1) || lua_isnumber(ls, 1)))
			{
				luaL_argerror(ls, 1, oxorany("Function or Number expected."));
			}

			int level;
			if (lua_isnumber(ls, 1))
			{
				level = lua_tointeger(ls, 1);
			}
			else
			{
				level = -lua_gettop(ls);
			}

			auto desc = lua_isstring(ls, 2) ? lua_tolstring(ls, 2, NULL) : "sluanf";

			lua_Debug ar;
			if (!lua_getinfo(ls, level, desc, &ar))
			{
				luaL_argerror(ls, 1, oxorany("Invalid stack level."));
			}

			if (!lua_isfunction(ls, -1))
			{
				luaL_argerror(ls, 1, oxorany("Stack is not pointing to a function."));
			}

			lua_newtable(ls);
			{
				if (std::strchr(desc, 's'))
				{
					lua_pushstring(ls, ar.source);
					lua_setfield(ls, -2, "source");

					lua_pushstring(ls, ar.short_src);
					lua_setfield(ls, -2, "short_src");

					lua_pushstring(ls, ar.what);
					lua_setfield(ls, -2, "what");

					lua_pushinteger(ls, ar.linedefined);
					lua_setfield(ls, -2, "linedefined");
				}

				if (std::strchr(desc, 'l'))
				{
					lua_pushinteger(ls, ar.currentline);
					lua_setfield(ls, -2, "currentline");
				}

				if (std::strchr(desc, 'u'))
				{
					lua_pushinteger(ls, ar.nupvals);
					lua_setfield(ls, -2, "nups");
				}

				if (std::strchr(desc, 'a'))
				{
					lua_pushinteger(ls, ar.isvararg);
					lua_setfield(ls, -2, "is_vararg");

					lua_pushinteger(ls, ar.nparams);
					lua_setfield(ls, -2, "numparams");
				}

				if (std::strchr(desc, 'n'))
				{
					lua_pushstring(ls, ar.name);
					lua_setfield(ls, -2, "name");
				}

				if (std::strchr(desc, 'f'))
				{
					lua_pushvalue(ls, -2);
					lua_remove(ls, -3);
					lua_setfield(ls, -2, "func");
				}
			}

			return 1;
		}

		int debug_getregistry(lua_State* L) {
			lua_pushvalue(L, LUA_REGISTRYINDEX);
			return 1;
		}
	}

	namespace Instance {

		template< class t >
		class c_storage
		{
			std::mutex m_l;

		protected:
			t m_container;
		public:

			auto safe_request(auto request, auto... args)
			{
				std::unique_lock l{ m_l };

				return request(args...);
			};

			void clear()
			{
				safe_request([&]()
					{ m_container.clear(); });
			}
		};

		using instance_cache_t
			= std::unordered_map< void*,
			std::unordered_map< std::string, bool > >;

		class c_instance_cache : public c_storage< instance_cache_t >
		{
		public:
			void toggle(void* instance, const std::string& prop, bool enabled)
			{
				safe_request([&]()
					{
						m_container[instance][prop] = enabled;
					});
			}

			std::optional< bool > is_scriptable(void* instance, const std::string& prop)
			{
				return safe_request([&]() -> std::optional< bool >
					{
						if (m_container.contains(instance))
						{
							const auto properties = m_container[instance];

							if (properties.contains(prop))
								return properties.at(prop);
						}

						return std::nullopt;
					});
			}
		} inline g_instance;

		__forceinline bool lua_isscriptable(lua_State* L, uintptr_t property)
		{
			auto scriptable = *reinterpret_cast<__int64*>(property + 64);
			return scriptable & 0x20;
		}

		__forceinline void lua_setscriptable(lua_State* L, uintptr_t property, bool enabled)
		{
			*reinterpret_cast<int*>(property + 64) = enabled ? 0xFF : 0;
		}

		int getinstancelist(lua_State* L) {
			lua_pushvalue(L, LUA_REGISTRYINDEX);
			lua_pushlightuserdata(L, (void*)rcv::PushInstance);
			lua_gettable(L, -2);
			return 1;
		}

		int gethwid(lua_State* L) {
			std::optional<std::string> hwid = GetHwid();

			if (hwid.has_value()) {
				lua_pushstring(L, hwid->c_str());
			}
			else {
				lua_pushnil(L);
			}

			return 1;
		}

		int isluau(lua_State* L) {
			lua_getglobal(L, "_VERSION");
			std::string version = lua_tostring(L, -1);
			lua_pop(L, 1);

			std::transform(version.begin(), version.end(), version.begin(), ::tolower);

			lua_pushboolean(L, version.find("luau") != std::string::npos);
			return 1;
		}
		int getnilinstances(lua_State* rl) {

			struct instance_context {
				lua_State* rl;
				std::intptr_t n;
			} context = { rl, 0 };

			lua_newtable(rl);

			for (lua_Page* page = rl->global->allgcopages; page;) {
				lua_Page* next{ page->listnext };

				luaM_visitpage(page, &context,
					[](void* context, lua_Page* page, GCObject* gco) -> bool {
						instance_context* gcContext{ reinterpret_cast<instance_context*>(context) };
						auto type = gco->gch.tt;

						if (type == LUA_TUSERDATA) {


							TValue* top = gcContext->rl->top;
							top->value.p = reinterpret_cast<void*>(gco);
							top->tt = type;
							gcContext->rl->top++;

							if (!strcmp(luaL_typename(gcContext->rl, -1), "Instance")) {
								lua_getfield(gcContext->rl, -1, "Parent");
								bool nullParent = lua_isnoneornil(gcContext->rl, -1);

								if (nullParent) {
									lua_pop(gcContext->rl, 1);
									gcContext->n++;
									lua_rawseti(gcContext->rl, -2, gcContext->n);
								}
								else {
									lua_pop(gcContext->rl, 2);
								}
							}
							else {
								lua_pop(gcContext->rl, 1);
							}
						}

						return true;
					}
				);

				page = next;
			}
			return 1;
		}

		auto getinstances(lua_State* rl) -> int
		{
			struct instance_context {
				lua_State* rl;
				std::intptr_t n;
			} context = { rl, 0 };

			lua_newtable(rl);
			for (lua_Page* page = rl->global->allgcopages; page;) {
				lua_Page* next{ page->listnext };

				luaM_visitpage(page, &context,
					[](void* context, lua_Page* page, GCObject* gco) -> bool {
						instance_context* gcContext{ reinterpret_cast<instance_context*>(context) };
						auto type = gco->gch.tt;

						if (type == LUA_TUSERDATA) {


							TValue* top = gcContext->rl->top;
							top->value.p = reinterpret_cast<void*>(gco);
							top->tt = type;
							gcContext->rl->top++;

							if (!strcmp(luaL_typename(gcContext->rl, -1), "Instance")) {
								gcContext->n++;
								lua_rawseti(gcContext->rl, -2, gcContext->n);
							}
							else {
								lua_pop(gcContext->rl, 1);
							}
						}

						return true;
					}
				);
				page = next;
			}
			return 1;
		}

		enum FastVarType : __int32
		{
			FASTVARTYPE_INVALID = 0x0,
			FASTVARTYPE_STATIC = 0x1,
			FASTVARTYPE_Env = 0x2,
			FASTVARTYPE_SYNC = 0x4,
			FASTVARTYPE_AB_NEWUSERS = 0x8,
			FASTVARTYPE_AB_NEWSTUDIOUSERS = 0x10,
			FASTVARTYPE_AB_ALLUSERS = 0x20,
			FASTVARTYPE_LOCAL_LOCKED = 0x40,
			FASTVARTYPE_ANY = 0x7F,
		};

		enum ReflectionType : uint32_t
		{
			ReflectionType_Void = 0x0,
			ReflectionType_Bool = 0x1,
			ReflectionType_Int = 0x2,
			ReflectionType_Int64 = 0x3,
			ReflectionType_Float = 0x4,
			ReflectionType_Double = 0x5,
			ReflectionType_String = 0x6,
			ReflectionType_ProtectedString = 0x7,
			ReflectionType_Instance = 0x8,
			ReflectionType_Instances = 0x9,
			ReflectionType_Ray = 0xa,
			ReflectionType_Vector2 = 0xb,
			ReflectionType_Vector3 = 0xc,
			ReflectionType_Vector2Int16 = 0xd,
			ReflectionType_Vector3Int16 = 0xe,
			ReflectionType_Rect2d = 0xf,
			ReflectionType_CoordinateFrame = 0x10,
			ReflectionType_Color3 = 0x11,
			ReflectionType_Color3uint8 = 0x12,
			ReflectionType_UDim = 0x13,
			ReflectionType_UDim2 = 0x14,
			ReflectionType_Faces = 0x15,
			ReflectionType_Axes = 0x16,
			ReflectionType_Region3 = 0x17,
			ReflectionType_Region3Int16 = 0x18,
			ReflectionType_CellId = 0x19,
			ReflectionType_GuidData = 0x1a,
			ReflectionType_PhysicalProperties = 0x1b,
			ReflectionType_BrickColor = 0x1c,
			ReflectionType_SystemAddress = 0x1d,
			ReflectionType_BinaryString = 0x1e,
			ReflectionType_Surface = 0x1f,
			ReflectionType_Enum = 0x20,
			ReflectionType_Property = 0x21,
			ReflectionType_Tuple = 0x22,
			ReflectionType_ValueArray = 0x23,
			ReflectionType_ValueTable = 0x24,
			ReflectionType_ValueMap = 0x25,
			ReflectionType_Variant = 0x26,
			ReflectionType_GenericFunction = 0x27,
			ReflectionType_WeakFunctionRef = 0x28,
			ReflectionType_ColorSequence = 0x29,
			ReflectionType_ColorSequenceKeypoint = 0x2a,
			ReflectionType_NumberRange = 0x2b,
			ReflectionType_NumberSequence = 0x2c,
			ReflectionType_NumberSequenceKeypoint = 0x2d,
			ReflectionType_InputObject = 0x2e,
			ReflectionType_Connection = 0x2f,
			ReflectionType_ContentId = 0x30,
			ReflectionType_DescribedBase = 0x31,
			ReflectionType_RefType = 0x32,
			ReflectionType_QFont = 0x33,
			ReflectionType_QDir = 0x34,
			ReflectionType_EventInstance = 0x35,
			ReflectionType_TweenInfo = 0x36,
			ReflectionType_DockWidgetPluginGuiInfo = 0x37,
			ReflectionType_PluginDrag = 0x38,
			ReflectionType_Random = 0x39,
			ReflectionType_PathWaypoint = 0x3a,
			ReflectionType_FloatCurveKey = 0x3b,
			ReflectionType_RotationCurveKey = 0x3c,
			ReflectionType_SharedString = 0x3d,
			ReflectionType_DateTime = 0x3e,
			ReflectionType_RaycastParams = 0x3f,
			ReflectionType_RaycastResult = 0x40,
			ReflectionType_OverlapParams = 0x41,
			ReflectionType_LazyTable = 0x42,
			ReflectionType_DebugTable = 0x43,
			ReflectionType_CatalogSearchParams = 0x44,
			ReflectionType_OptionalCoordinateFrame = 0x45,
			ReflectionType_CSGPropertyData = 0x46,
			ReflectionType_UniqueId = 0x47,
			ReflectionType_Font = 0x48,
			ReflectionType_Blackboard = 0x49,
			ReflectionType_Max = 0x4a
		};

		namespace Concepts
		{
			template<typename Derived, typename Base>
			concept _TypeConstraint = std::is_base_of_v<Base, Derived>;
		}

		struct Descriptor
		{
			enum ThreadSafety : uint32_t { Unset = 0x0, Unsafe = 0x1, ReadSafe = 0x3, LocalSafe = 0x7, Safe = 0xf };
			struct Attributes
			{
				bool isDeprecated;
				class Descriptor* preferred;
				enum ThreadSafety threadSafety;
			};
			void* vftable;
			std::string& name;
			struct Attributes attributes;
		};

		struct MemberDescriptor : Descriptor
		{
			std::string& category;
			class ClassDescriptor* owner;
			enum Permissions permissions;
			int32_t _0;
		};

		struct Type : Descriptor
		{
			std::string& tag;
			enum ReflectionType reflectionType;
			bool isFloat;
			bool isNumber;
			bool isEnum;
			bool isOptional;
		};

		struct EventDescriptor : MemberDescriptor {};
		struct PropertyDescriptorVFT {};
		struct PropertyDescriptor : MemberDescriptor
		{
		public:
			union {
				uint32_t bIsEditable;
				uint32_t bCanReplicate;
				uint32_t bCanXmlRead;
				uint32_t bCanXmlWrite;
				uint32_t bAlwaysClone;
				uint32_t bIsScriptable;
				uint32_t bIsPublic;
			} __bitfield;
			Type* type;
			bool bIsEnum;
			Permissions scriptWriteAccess;

			bool IsScriptable() { return (this->__bitfield.bIsScriptable > 0x20) & 1; }

			void SetScriptable(const uint8_t bIsScriptable)
			{
				this->__bitfield.bIsScriptable = (this->__bitfield.bIsScriptable) ^ (bIsScriptable ? 33 : 32);
			}

			bool IsEditable() { return ((this->__bitfield.bIsEditable) & 1); }

			void SetEditable(const uint8_t bIsEditable)
			{
				this->__bitfield.bIsEditable = (this->__bitfield.bIsEditable) ^ ((~bIsEditable & 0xFF));
			}

			bool IsCanXmlRead() { return ((this->__bitfield.bCanXmlRead >> 3) & 1); }
			void SetCanXmlRead(const uint8_t bCanXmlRead)
			{
				this->__bitfield.bCanXmlRead = (this->__bitfield.bCanXmlRead) ^ ((~bCanXmlRead & 0xFF << 3));
			}

			bool IsCanXmlWrite() { return ((this->__bitfield.bCanXmlWrite >> 4) & 1); }
			void SetCanXmlWrite(const uint8_t bCanXmlWrite)
			{
				this->__bitfield.bCanXmlWrite = (this->__bitfield.bCanXmlWrite) ^ ((~bCanXmlWrite & 0xFF << 4));
			}

			bool IsPublic() { return ((this->__bitfield.bIsPublic >> 6) & 1); }
			void SetIsPublic(const uint8_t bIsPublic)
			{
				this->__bitfield.bIsPublic =
					(this->__bitfield.bIsPublic) ^ static_cast<uint32_t>(~bIsPublic & 0xFF << 6);
			}

			bool IsCanReplicate() { return ((this->__bitfield.bCanReplicate >> 2) & 1); }
			void SetCanReplicate(const uint8_t bCanReplicate)
			{
				this->__bitfield.bCanReplicate = (this->__bitfield.bCanReplicate) ^ ((~bCanReplicate & 0xFF << 2));
			}

			bool IsAlwaysClone() { return ((this->__bitfield.bAlwaysClone) & 1); }
			void SetAlwaysClone(const uint8_t bAlwaysClone)
			{
				this->__bitfield.bAlwaysClone = (this->__bitfield.bAlwaysClone) ^ (~bAlwaysClone & 0xFF);
			}

			PropertyDescriptorVFT* GetVFT() { return static_cast<PropertyDescriptorVFT*>(this->vftable); }
		};

		template<Concepts::_TypeConstraint<MemberDescriptor> U>
		struct MemberDescriptorContainer
		{
			std::vector<U*> descriptors;
			const char _0[144];
		};

		struct ClassDescriptor;
		struct ClassDescriptor : Descriptor
		{
			MemberDescriptorContainer<PropertyDescriptor> propertyDescriptors;
			MemberDescriptorContainer<EventDescriptor> eventDescriptors;
			void* boundFunctionDescription_Start;
			char _180[0x40];
			char _1c0[0x40];
			char _200[0x20];
			void* boundYieldFunctionDescription_Start;
			char _228[0x18];
			char _240[0x40];
			char _280[0x40];
			char _2c0[8];
			char _2c8[0x38];
			char _300[0x40];
			char _340[0x30];
			char _370[8];
			char _378[8];
			char _380[4];
			char _384[2];
			char _386[2];
			char _388[8];
			struct ClassDescriptor* baseClass;
			char _398[8];
			char _3a0[8];
			char _3a8[0x18];
			char _3c0[0x20];
		};
		struct Instance
		{
			void* vftable;
			std::weak_ptr<Instance> self;
			ClassDescriptor* classDescriptor;
		};

		std::vector<std::tuple<uintptr_t, std::string, bool>> script_able_cache;
		std::vector<std::pair<std::string, bool>> default_property_states;

		int getCachedScriptableProperty(uintptr_t instance, std::string property) {
			for (auto& cacheData : script_able_cache) {
				uintptr_t instanceAddress = std::get<0>(cacheData);
				std::string instanceProperty = std::get<1>(cacheData);

				if (instanceAddress == instance && instanceProperty == property) {
					return std::get<2>(cacheData);
				}
			}

			return -1;
		};

		int getCachedDefultScriptableProperty(std::string property) {
			for (auto& cacheData : default_property_states) {
				if (cacheData.first == property) {
					return cacheData.second;
				}
			}

			return -1;
		};

		void addDefaultPropertyState(std::string property, bool state) {
			bool hasDefault = false;

			for (auto& cacheData : default_property_states) {
				if (cacheData.first == property) {
					hasDefault = true;
					break;
				}
			}

			if (!hasDefault) {
				default_property_states.push_back({ property, state });
			}
		};

		bool findAndUpdateScriptAbleCache(uintptr_t instance, std::string property, bool state) {
			for (auto& cacheData : script_able_cache) {
				uintptr_t instanceAddress = std::get<0>(cacheData);
				std::string instanceProperty = std::get<1>(cacheData);

				if (instanceAddress == instance && instanceProperty == property) {
					std::get<2>(cacheData) = state;
					return true;
				}
			}

			return false;
		}

		auto setscriptable(lua_State* L)
		{
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TSTRING);
			luaL_checktype(L, 3, LUA_TBOOLEAN);

			const auto userData = lua_touserdata(L, 1);
			const auto InstancePtr = *reinterpret_cast<uintptr_t*>(userData);
			const auto scriptableBool = lua_toboolean(L, 3);

			int Atom;
			auto Property = lua_tostringatom(L, 2, &Atom);

			const auto KTable = (uintptr_t*)rcv::KTable;
			auto Descriptor = KTable[Atom];
			if (!Descriptor) {
				lua_pushnil(L);
				return 1;
			}

			auto ClassDescriptor = *(uintptr_t*)(InstancePtr + 0x18);
			const auto Prop = rcv::defs::GetProperty(ClassDescriptor + 0x3B0, &Descriptor);
			if (!Prop) {
				lua_pushboolean(L, false);
				return 1;
			}

			if (!findAndUpdateScriptAbleCache(InstancePtr, Property, scriptableBool))
				script_able_cache.push_back({ InstancePtr, Property, scriptableBool });

			std::uint64_t scriptable = *reinterpret_cast<std::uint64_t*>(*Prop + 0x40);
			bool wasScriptAble = scriptable & 0x20;

			addDefaultPropertyState(Property, scriptable & 0x20);

			*reinterpret_cast<std::uint64_t*>(*Prop + 0x40) = std::bitset< 32 >{ scriptable }.set(5, scriptableBool).to_ulong();
			lua_pushboolean(L, wasScriptAble);
			return 1;
		}

		int isscriptable(lua_State* L)
		{
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TSTRING);

			const auto userData = lua_touserdata(L, 1);
			const auto InstancePtr = *reinterpret_cast<uintptr_t*>(userData);

			int Atom;
			auto Property = lua_tostringatom(L, 2, &Atom);

			const auto KTable = (uintptr_t*)rcv::KTable;
			auto Descriptor = KTable[Atom];
			if (!Descriptor) {
				lua_pushnil(L);
				return 1;
			}

			auto ClassDescriptor = *(uintptr_t*)(InstancePtr + 0x18);
			const auto Prop = rcv::defs::GetProperty(ClassDescriptor + 0x3B0, &Descriptor);
			if (!Prop) {
				lua_pushboolean(L, false);
				return 1;
			}

			int cachedProperty = getCachedScriptableProperty(InstancePtr, Property);
			int cachedDefaultProperty = getCachedDefultScriptableProperty(Property);

			if (cachedProperty != -1) {
				lua_pushboolean(L, cachedProperty);
				return 1;
			}

			if (cachedDefaultProperty != -1) {
				lua_pushboolean(L, cachedDefaultProperty);
				return 1;
			}

			std::uint64_t scriptable = *reinterpret_cast<std::uint64_t*>(*Prop + 0x40);
			lua_pushboolean(L, scriptable & 0x20);

			return 1;
		}

		static const char* GetStringFromSharedString(const auto* sharedString)
		{
			if (!sharedString) return nullptr; // Prevent null dereferencing

			auto sharedDeref = reinterpret_cast<const void* const*>(sharedString);
			return reinterpret_cast<const char*>(reinterpret_cast<const char*>(sharedDeref) + 0x10);
		}

		auto gethiddenproperty(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TUSERDATA);
			luaL_checktype(rl, 2, LUA_TSTRING);

			uintptr_t instance = reinterpret_cast<uintptr_t>(lua_touserdata(rl, 1));
			std::string property_name = lua_tostring(rl, 2);

			uintptr_t object;
			bool found;
			std::vector<uintptr_t> properties = *reinterpret_cast<std::vector<uintptr_t>*>(reinterpret_cast<uintptr_t*>(instance + 24) + 40);
			for (int i = 0; i < properties.size(); i++)
			{
				uintptr_t property = properties[i];
				if (property_name == *reinterpret_cast<std::string*>(reinterpret_cast<uintptr_t*>(property + 8)))
				{
					object = property;

					found = true;
					break;
				}
			}

			if (found == false)
				luaL_error(rl, "Property not exists.");

			std::string propertyTypeName = *(std::string*)((uintptr_t*)(object + 0x48) + 0x8);

			int propertyType = (int)((uintptr_t)(object + 0x48) + 0x30);
			if (!strcmp(propertyTypeName.c_str(), "BinaryString")) {
				*(int*)((uintptr_t*)(object + 0x48) + 0x30) = 6;
			}

			if (!strcmp(propertyTypeName.c_str(), "SharedString")) {
				*(int*)((uintptr_t*)(object + 0x48) + 0x10) = 6;
			}

			bool scriptable = lua_isscriptable(rl, object);
			int original_value = *reinterpret_cast<int*>(object + 64);
			if (scriptable == true)
			{
				lua_getfield(rl, 1, property_name.c_str());
				lua_pushboolean(rl, false);
				return 2;
			}
			else
			{
				lua_setscriptable(rl, object, true);
				lua_getfield(rl, 1, property_name.c_str());
				lua_pushboolean(rl, true);
				lua_setscriptable(rl, object, false);
				return 2;
			}
		}

		int gethiddenproperty1(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TSTRING);

			std::string PropName = lua_tostring(L, 2);
			const auto rbxInstance = *reinterpret_cast<Instance**>(lua_touserdata(L, 1));

			ReflectionType oldPropType;

			for (const auto& Prop : rbxInstance->classDescriptor->propertyDescriptors.descriptors) {
				if (Prop->name == PropName && Prop->type->reflectionType == ReflectionType::ReflectionType_BinaryString) {
					oldPropType = ReflectionType::ReflectionType_BinaryString;
					Prop->type->reflectionType = ReflectionType::ReflectionType_String;
					break;
				}
			}

			lua_pushcclosure(L, isscriptable, 0, 0);
			lua_pushvalue(L, 1);
			lua_pushstring(L, PropName.c_str());
			lua_call(L, 2, 1);

			const auto was = lua_toboolean(L, -1);
			lua_pop(L, 1);

			lua_pushcclosure(L, setscriptable, 0, 0);
			lua_pushvalue(L, 1);
			lua_pushstring(L, PropName.c_str());
			lua_pushboolean(L, true);
			lua_pcall(L, 3, 1, 0);
			lua_pop(L, 1);

			lua_getfield(L, 1, PropName.c_str());
			lua_pushboolean(L, !was);

			lua_pushcclosure(L, setscriptable, 0, 0);
			lua_pushvalue(L, 1);
			lua_pushstring(L, PropName.c_str());
			lua_pushboolean(L, was);
			lua_pcall(L, 3, 1, 0);
			lua_pop(L, 1);

			if (oldPropType == ReflectionType::ReflectionType_BinaryString) {
				for (const auto& Prop : rbxInstance->classDescriptor->propertyDescriptors.descriptors) {

					if (Prop->name == PropName) {
						Prop->type->reflectionType = oldPropType;
						break;
					}
				}
			}

			return 2;
		}

		int sethiddenproperty1(lua_State* L) {
			luaL_checktype(L, 1, LUA_TUSERDATA);
			luaL_checktype(L, 2, LUA_TSTRING);
			luaL_checkany(L, 3);

			std::string PropName = lua_tostring(L, 2);

			lua_pushcclosure(L, isscriptable, 0, 0);
			lua_pushvalue(L, 1);
			lua_pushstring(L, PropName.c_str());
			lua_call(L, 2, 1);

			const auto was = lua_toboolean(L, -1);
			lua_pop(L, 1);

			lua_pushcclosure(L, setscriptable, 0, 0);
			lua_pushvalue(L, 1);
			lua_pushstring(L, PropName.c_str());
			lua_pushboolean(L, true);
			lua_pcall(L, 3, 1, 0);
			lua_pop(L, 1);

			lua_pushvalue(L, 3);
			lua_setfield(L, 1, PropName.c_str());
			lua_pushboolean(L, !was);

			lua_pushcclosure(L, setscriptable, 0, 0);
			lua_pushvalue(L, 1);
			lua_pushstring(L, PropName.c_str());
			lua_pushboolean(L, was);
			lua_pcall(L, 3, 1, 0);
			lua_pop(L, 1);

			return 1;
		};

		auto sethiddenproperty(lua_State* rl) -> int
		{
			luaL_checktype(rl, 1, LUA_TUSERDATA);
			luaL_checktype(rl, 2, LUA_TSTRING);

			uintptr_t instance = *reinterpret_cast<uintptr_t*>(lua_touserdata(rl, 1));
			std::string property_name = lua_tostring(rl, 2);

			uintptr_t object;
			bool found;
			std::vector<uintptr_t> properties = *reinterpret_cast<std::vector<uintptr_t>*>(*reinterpret_cast<uintptr_t*>(instance + 24) + 40);
			for (int i = 0; i < properties.size(); i++)
			{
				uintptr_t property = properties[i];
				if (property_name == *reinterpret_cast<std::string*>(*reinterpret_cast<uintptr_t*>(property + 8)))
				{
					object = property;
					found = true;
					break;
				}
			}

			if (found == false)
				luaL_error(rl, "Property not exists.");

			std::string propertyTypeName = *(std::string*)((uintptr_t*)(object + 0x48) + 0x8);

			int propertyType = (int)((uintptr_t)(object + 0x48) + 0x30);
			if (!strcmp(propertyTypeName.c_str(), "BinaryString")) {
				*(int*)((uintptr_t*)(object + 0x48) + 0x30) = 6;
			}

			bool scriptable = lua_isscriptable(rl, object);
			int original_value = *reinterpret_cast<int*>(object + 64);
			if (scriptable == true)
			{
				lua_pushvalue(rl, 3);
				lua_setfield(rl, 1, property_name.c_str());
				lua_pushboolean(rl, false);
				lua_setscriptable(rl, object, false);
				return 1;
			}
			else
			{
				lua_setscriptable(rl, object, true);
				lua_pushvalue(rl, 3);
				lua_setfield(rl, 1, property_name.c_str());
				lua_pushboolean(rl, true);
				lua_setscriptable(rl, object, false);
				return 1;
			}
		}


		__forceinline int getscripts(lua_State* L) {
			struct instancecontext {
				lua_State* L;
				__int64 n;
			} Context = { L, 0 };

			lua_createtable(L, 0, 0);

			const auto ullOldThreshold = L->global->GCthreshold;
			L->global->GCthreshold = SIZE_MAX; // Disable GC temporarily

			luaM_visitgco(L, &Context, [](void* ctx, lua_Page* page, GCObject* gco) -> bool {
				auto gCtx = static_cast<instancecontext*>(ctx);
				const auto type = gco->gch.tt;

				if (isdead(gCtx->L->global, gco))
					return false;

				if (type == LUA_TUSERDATA) {

					TValue* top = gCtx->L->top;
					top->value.p = reinterpret_cast<void*>(gco);
					top->tt = type;
					gCtx->L->top++;

					if (!strcmp(luaL_typename(gCtx->L, -1), "Instance")) { // instance check
						lua_getfield(gCtx->L, -1, "ClassName"); // check if instance has no parent / basically nil instance

						const char* inst_class = lua_tolstring(gCtx->L, -1, 0);
						if (!strcmp(inst_class, "LocalScript") || !strcmp(inst_class, "ModuleScript") ||
							!strcmp(inst_class, "CoreScript") || !strcmp(inst_class, "Script")) {
							lua_pop(gCtx->L, 1);
							gCtx->n++;
							lua_rawseti(gCtx->L, -2, gCtx->n);
						}
						else
							lua_pop(gCtx->L, 2);

					}
					else {
						lua_pop(gCtx->L, 1);
					}
				}

				return true;
				});

			L->global->GCthreshold = ullOldThreshold;

			return 1;
		}
	}
}
namespace MetaHooks
{
	static __int64 old_namecall;
	static __int64 old_index;

	std::vector<const char*> dangerous_functions =
	{
		"OpenVideosFolder", "OpenScreenshotsFolder", "GetRobuxBalance", "PerformPurchase",
		"PromptBundlePurchase", "PromptNativePurchase", "PromptProductPurchase", "PromptPurchase",
		"PromptThirdPartyPurchase", "Publish", "GetMessageId", "OpenBrowserWindow",
		"RequestInternal", "ExecuteJavaScript", "ToggleRecording", "TakeScreenshot",
		"HttpRequestAsync", "GetLast", "SendCommand", "GetAsync", "GetAsyncFullUrl",
		"RequestAsync", "MakeRequest", "PostAsync", "HttpPost", "PostAsyncFullUrl",
		"PerformPurchaseV2", "PromptGamePassPurchase", "PromptRobloxPurchase",
		"OpenNativeOverlay", "AddCoreScriptLocal", "EmitHybridEvent", "ReturnToJavaScript",
		"Call", "OpenUrl", "SaveScriptProfilingData", "GetProtocolMethodRequestMessageId",
		"GetProtocolMethodResponseMessageId", "PublishProtocolMethodRequest",
		"PublishProtocolMethodResponse", "Subscribe", "SubscribeToProtocolMethodRequest",
		"SubscribeToProtocolMethodResponse", "PromptNativePurchaseWithLocalPlayer",
		"PromptCollectiblesPurchase", "PerformBulkPurchase", "PerformCancelSubscription",
		"PerformSubscriptionPurchase", "PerformSubscriptionPurchaseV2",
		"PrepareCollectiblesPurchase", "PromptBulkPurchase", "PromptCancelSubscription",
		"PromptPremiumPurchase", "PromptSubscriptionPurchase", "OpenWeChatAuthWindow",
		"RequestLimitedAsync", "Run", "CaptureScreenshot", "CreatePostAsync",
		"DeleteCapture", "DeleteCapturesAsync", "GetCaptureFilePathAsync",
		"SaveCaptureToExternalStorage", "SaveCapturesToExternalStorageAsync",
		"GetCaptureUploadDataAsync", "RetrieveCaptures", "SaveScreenshotCapture",
		"GetCredentialsHeaders", "GetDeviceIntegrityToken", "GetDeviceIntegrityTokenYield",
		"NoPromptCreateOutfit", "NoPromptDeleteOutfit", "NoPromptRenameOutfit",
		"NoPromptSaveAvatar", "NoPromptSaveAvatarThumbnailCustomization", "NoPromptSetFavorite",
		"NoPromptUpdateOutfit", "PerformCreateOutfitWithDescription", "PerformRenameOutfit",
		"PerformSaveAvatarWithDescription", "PerformSetFavorite", "PerformUpdateOutfit",
		"PromptCreateOutfit", "PromptDeleteOutfit", "PromptRenameOutfit", "PromptSaveAvatar",
		"PromptSetFavorite", "PromptUpdateOutfit", "PromptImportFile", "PromptImportFiles",
		"GetUsersubscriptionPaymentHistoryAsync", "GetUserSubscriptionDetailsInternalAsync",
		"CallFunction", "BindCoreActive", "ReportAbuse", "ReportAbuseV3", "ReportChatAbuse"
	};

	auto dangerous_function(lua_State* L) -> int
	{
		luaL_error(L, "Attempt to call blocked function");
		return 0;
	}

	auto dangerous_service(lua_State* L) -> int
	{
		luaL_error(L, "Attempt to get a blocked Service");
		return 0;
	}

	std::string toLower(const std::string& str) {
		std::string lowerStr = str;
		std::transform(lowerStr.begin(), lowerStr.end(), lowerStr.begin(), ::tolower);
		return lowerStr;
	}

	auto namecall_hook(lua_State* L) -> int
	{
		const auto script_ptr = *reinterpret_cast<std::uintptr_t*>(reinterpret_cast<std::uintptr_t>(L->userdata) + rcv::offsets::Script);

		if (L->namecall && !script_ptr)
		{
			const char* data = L->namecall->data;

			if (!strcmp(data, "HttpGet") || !strcmp(data, "HttpGetAsync"))
			{
				return Env::HTTP::httpget(L);
			}

			if (!strcmp(data, "GetObjects") || !strcmp(data, "GetObjectsAsync"))
			{
				return Env::Scripts::getobjects(L);
			}

			for (unsigned int i = 0; i < dangerous_functions.size(); i++) {
				if (toLower(data) == toLower(dangerous_functions[i])) {
					luaL_error(L, "Attempt to call blocked function (%s)", data);
				}
			}
		}

		return reinterpret_cast<__int64(__fastcall*)(__int64)>(old_namecall)((__int64)L);
	}

	auto index_hook(lua_State* L) -> int
	{
		auto state = (__int64)L;
		const auto script_ptr = *reinterpret_cast<std::uintptr_t*>(reinterpret_cast<std::uintptr_t>(L->userdata) + rcv::offsets::Script);

		uintptr_t userdata = *reinterpret_cast<uintptr_t*>(state + 120);
		int level = *reinterpret_cast<uintptr_t*>(userdata + 0x30);

		if (lua_isstring(L, 2) && !script_ptr)
		{
			const char* data = luaL_checkstring(L, 2);

			if (!strcmp(data, "HttpGet") || !strcmp(data, "HttpGetAsync"))
			{
				lua_getglobal(L, "httpget");
				return 1;
			}

			if (!strcmp(data, "GetObjects") || !strcmp(data, "GetObjectsAsync"))
			{
				lua_getglobal(L, "getobjects");
				return 1;
			}

			for (unsigned int i = 0; i < dangerous_functions.size(); i++) {
				if (toLower(data) == toLower(dangerous_functions[i])) {
					lua_pushcclosure(L, dangerous_function, NULL, 0);
					return 1;
				}
			}
		}

		return reinterpret_cast<__int64(__fastcall*)(__int64)>(old_index)((__int64)L);
	}

	auto initialize(lua_State* L) -> void // OPPPPPP HOOK!!!!
	{
		lua_getglobal(L, "game");
		lua_getmetatable(L, -1);
		lua_getfield(L, -1, "__namecall");

		Closure* namecall = (Closure*)lua_topointer(L, -1);
		lua_CFunction namecall_f = namecall->c.f;
		old_namecall = (__int64)namecall_f;
		namecall->c.f = namecall_hook;

		lua_settop(L, 0);

		lua_getglobal(L, "game");
		lua_getmetatable(L, -1);
		lua_getfield(L, -1, "__index");

		Closure* index = (Closure*)lua_topointer(L, -1);
		lua_CFunction index_f = index->c.f;
		old_index = (__int64)index_f;
		index->c.f = index_hook;
	}
}

namespace Bit {
	int bit_band(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int b = luaL_checkinteger(L, 2);
		lua_pushinteger(L, a & b);
		return 1;
	}

	int bit_bor(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int b = luaL_checkinteger(L, 2);
		lua_pushinteger(L, a | b);
		return 1;
	}

	int bit_bxor(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int b = luaL_checkinteger(L, 2);
		lua_pushinteger(L, a ^ b);
		return 1;
	}

	int bit_bnot(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		lua_pushinteger(L, ~a);
		return 1;
	}

	int bit_lshift(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int shift = luaL_checkinteger(L, 2);
		lua_pushinteger(L, a << shift);
		return 1;
	}

	int bit_blshift(lua_State* L)
	{
		int val = lua_tointeger(L, -2, 0);
		int by = lua_tointeger(L, -1, 0);
		int ret = val << by;

		lua_pushinteger(L, ret);

		return 1;
	}

	int bit_brshift(lua_State* L)
	{
		int val = lua_tointeger(L, -2, 0);
		int by = lua_tointeger(L, -1, 0);
		int ret = val >> by;

		lua_pushinteger(L, ret);

		return 1;
	}

	int bit_rshift(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int shift = luaL_checkinteger(L, 2);
		lua_pushinteger(L, a >> shift);
		return 1;
	}

	int bit_rol(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int shift = luaL_checkinteger(L, 2);
		int bits = sizeof(a) * 8;
		lua_pushinteger(L, (a << shift) | (a >> (bits - shift)));
		return 1;
	}

	int bit_ror(lua_State* L) {
		int a = luaL_checkinteger(L, 1);
		int shift = luaL_checkinteger(L, 2);
		int bits = sizeof(a) * 8;
		lua_pushinteger(L, (a >> shift) | (a << (bits - shift)));
		return 1;
	}

	int bit_bmul(lua_State* L)
	{
		int val = lua_tointeger(L, -2, 0);
		int by = lua_tointeger(L, -1, 0);
		int ret = val * by;

		lua_pushinteger(L, ret);
		return 1;
	}

	int bit_bswap(lua_State* L)
	{

		int by = lua_tointeger(L, -1, 0);
		int ret = by >> 24 | by >> 8 & 0xff00 | (by & 0xff00) << 8 | by << 24;
		lua_pushinteger(L, ret);
		return 1;
	}

	int bit_bdiv(lua_State* L)
	{
		int val = lua_tointeger(L, -2, 0);
		int by = lua_tointeger(L, -1, 0);
		int ret = val / by;

		lua_pushinteger(L, ret);
		return 1;
	}

	int bit_badd(lua_State* L)
	{
		int val = lua_tointeger(L, -2, 0);
		int by = lua_tointeger(L, -1, 0);
		int ret = val + by;

		lua_pushinteger(L, ret);
		return 1;
	}

	int bit_bsub(lua_State* L)
	{
		int val = lua_tointeger(L, -2, 0);
		int by = lua_tointeger(L, -1, 0);
		int ret = val - by;

		lua_pushinteger(L, ret);
		return 1;
	}
}

namespace Actors {
	class bytecode_encoder_t1 : public Luau::BytecodeEncoder {
		inline void encode(uint32_t* data, size_t count) override {

			for (auto i = 0u; i < count;) {

				auto& opcode = *reinterpret_cast<uint8_t*>(data + i);

				i += Luau::getOpLength(LuauOpcode(opcode));

				opcode *= 227;
			}
		}
	};

	uintptr_t deobfuscate_proto(uintptr_t object) {
		return *reinterpret_cast<uintptr_t*>(object + 24) ^ (object + 24);
	}

	int getactors(lua_State* L) {
		std::map< uintptr_t, bool > map;

		lua_pushvalue(L, LUA_REGISTRYINDEX);

		lua_newtable(L);

		lua_pushnil(L);

		auto c = 0u;
		while (lua_next(L, -3))
		{
			if (lua_isuserdata(L, -1))
			{
				const auto userdata = lua_touserdata(L, -1);

				if (userdata)
				{
					if (!strcmp(luaL_typename(L, -1), "Instance")) {
						const auto instance = *(uintptr_t*)(userdata);
						if (instance) {
							const auto class_descriptor = *(uintptr_t*)(instance + 0x18);

							if (class_descriptor) {
								std::string class_name = **(std::string**)(class_descriptor + 0x8);

								if (!strcmp(class_name.c_str(), "Actor")) {
									if (map.find(instance) == map.end())
									{
										map.insert({ instance, true });

										rcv::defs::PushInstance(L, userdata);

										lua_rawseti(L, -4, ++c);
									}
								}
							}
						}
					}
				}
			}

			lua_pop(L, 1);
		}

		return 1;
	}

	bool checkparallel(uintptr_t arg) {
		return *(BYTE*)(*(uintptr_t*)(*(uintptr_t*)(arg + 0x18) + 0x8) + 0xF8);
	}

	int isparallel(lua_State* L) {
		if (L->userdata) {
			auto actor = reinterpret_cast<std::uintptr_t>(L->userdata);

			if (actor && rcv::offsets::Actor) {
				auto actor_offset = reinterpret_cast<std::uintptr_t*>(actor + rcv::offsets::Actor);
				if (actor_offset && *actor_offset != NULL) {
					return lua_pushboolean(L, true), 1;
				}
			}

			if (checkparallel && checkparallel(actor)) {
				return lua_pushboolean(L, true), 1;
			}
		}

		return lua_pushboolean(L, false), 1;
	}
}


namespace Replicator {
	class RBXScriptSignal {
	public:
		using Callback = std::function<void()>;

		void Connect(Callback callback) {
			connections.push_back(callback);
		}

		void Fire() {
			for (const auto& conn : connections) {
				conn();
			}
		}

		bool HasConnections() const {
			return !connections.empty();
		}

	private:
		std::vector<Callback> connections;
	};

	std::unordered_map<int, RBXScriptSignal> signalRegistry;

	int ReplicateSignal(lua_State* L) {
		if (!lua_isuserdata(L, 1)) {
			luaL_error(L, "replicatesignal: Invalid signal provided");
		}

		RBXScriptSignal* signal = *static_cast<RBXScriptSignal**>(lua_touserdata(L, 1));
		if (!signal || !signal->HasConnections()) {
			lua_pushboolean(L, false);
			return 1;
		}

		try {
			signal->Fire();
			lua_pushboolean(L, true);
		}
		catch (...) {
			lua_pushboolean(L, false);
		}

		return 1;
	}

	int RegisterSignal(lua_State* L) {
		static int signalID = 0;
		RBXScriptSignal* newSignal = new RBXScriptSignal();
		signalRegistry[++signalID] = *newSignal;
		lua_pushlightuserdata(L, newSignal);
		return 1;
	}
}

int messagebox(lua_State* L) {
	luaL_stackcheck(L, 3, 3);
	const auto text = luaL_checkstring(L, 1);
	const auto caption = luaL_checkstring(L, 2);
	const auto type = luaL_checkinteger(L, 3);

	return Scheduler::YieldExecution(L,
		[text, caption, type]() -> auto {

			const int lMessageboxReturn = MessageBoxA(nullptr, text, caption, type);

			return [lMessageboxReturn](lua_State* L) -> int {
				lua_pushinteger(L, lMessageboxReturn);
				return 1;
				};
		}
	);
}

namespace Properties {
	auto getproperties(lua_State* L) -> int {
		luaL_stackcheck(L, 1, 1, checkType(L, 1, LUA_TUSERDATA););
		if (strcmp(luaL_typename(L, 1), "Instance") != 0) {
			luaL_typeerror(L, 1, "Instance");
			return 0;
		}

		const auto instance = *reinterpret_cast<std::intptr_t*>(lua_touserdata(L, 1));
		const auto classDescriptor = *reinterpret_cast<std::intptr_t*>(instance + 0x18);

		lua_createtable(L, 0, 0);

		std::intptr_t tabPos = 0;
		for (std::intptr_t property : *reinterpret_cast<std::vector<std::intptr_t>*>(classDescriptor + 0x3B0)) {
			std::string propertyName = *reinterpret_cast<std::string*>(*reinterpret_cast<std::intptr_t*>(property + 0x48));

			lua_pushlstring(L, propertyName.c_str(), propertyName.size());
			lua_rawseti(L, -2, ++tabPos);
		}

		return 1;
	};

	auto gethiddenproperties(lua_State* L) -> int {
		luaL_stackcheck(L, 1, 1, checkType(L, 1, LUA_TUSERDATA););
		if (strcmp(luaL_typename(L, 1), "Instance") != 0) {
			luaL_typeerror(L, 1, "Instance");
			return 0;
		}

		const auto instance = *reinterpret_cast<std::intptr_t*>(lua_touserdata(L, 1));
		const auto classDescriptor = *reinterpret_cast<std::intptr_t*>(instance + 0x18);

		lua_createtable(L, 0, 0);

		std::intptr_t tabPos = 0;
		for (std::intptr_t property : *reinterpret_cast<std::vector<std::intptr_t>*>(classDescriptor + 0x3B0)) {
			std::string propertyName = *reinterpret_cast<std::string*>(*reinterpret_cast<std::intptr_t*>(property + 0x48));
			bool isScriptable = Env::Instance::lua_isscriptable(L, property); // 0x20

			if (isScriptable == false) {
				lua_pushlstring(L, propertyName.c_str(), propertyName.size());
				lua_rawseti(L, -2, ++tabPos);
			}
		}

		return 1;
	};
}

void Environment::Initiliaze(lua_State* L) {
	lua_newtable(L);
	lua_setglobal(L, "_G");

	lua_newtable(L);
	lua_setglobal(L, "shared");
	push_global(L, "getgenv", Env::Scripts::getgenv);
	push_global(L, "getreg", Env::Scripts::getreg);
	push_global(L, "getgc", Env::Scripts::getgc);
	push_global(L, "get_gc_collection", Env::Scripts::getgc);
	push_global(L, "get_gc_objects", Env::Scripts::getgc);
	push_global(L, "get_garbage_collection", Env::Scripts::getgc);
	push_global(L, "gettenv", Env::Scripts::gettenv);
	push_global(L, "getrenv", Env::Scripts::getrenv);
	push_global(L, "messagebox", messagebox);

	push_global(L, ("isexecutorclosure"), Env::Closures::is_executor_closure);
	push_global(L, ("isourclosure"), Env::Closures::is_executor_closure);
	push_global(L, ("checkclosure"), Env::Closures::is_executor_closure);
	push_global(L, ("clonefunction"), Env::Closures::clonefunction);
	push_global(L, ("clonefunc"), Env::Closures::clonefunction);
	push_global(L, ("hookfunction"), Env::Closures::hookfunction);
	push_global(L, ("replaceclosure"), Env::Closures::hookfunction);
	push_global(L, ("hookfunc"), Env::Closures::hookfunction);
	push_global(L, ("iscclosure"), Env::Closures::iscclosure);
	push_global(L, ("is_c_closure"), Env::Closures::iscclosure);
	push_global(L, ("islclosure"), Env::Closures::islclosure);
	push_global(L, ("is_l_closure"), Env::Closures::islclosure);
	push_global(L, ("checkcaller"), Env::Closures::checkcaller);
	push_global(L, ("isfunctionhooked"), Env::Closures::isfunctionhooked);
	push_global(L, ("restorefunction"), Env::Closures::restorefunction);
	push_global(L, ("hookmetamethod"), Env::Closures::hookmetamethod);

	push_global(L, "isrbxactive", Env::Input::isrbxactive);
	push_global(L, "isgameactive", Env::Input::isrbxactive);
	push_global(L, "iswindowactive", Env::Input::isrbxactive);
	push_global(L, "keypress", Env::Input::keypress);
	push_global(L, "keytap", Env::Input::keytap);
	push_global(L, "keyrelease", Env::Input::keyrelease);
	push_global(L, "mouse1click", Env::Input::mouse1click);
	push_global(L, "mouse1press", Env::Input::mouse1press);
	push_global(L, "mouse1release", Env::Input::mouse1release);
	push_global(L, "mouse2click", Env::Input::mouse2click);
	push_global(L, "mouse2press", Env::Input::mouse2press);
	push_global(L, "mouse2release", Env::Input::mouse2release);
	push_global(L, "mousemoveabs", Env::Input::mousemoveabs);
	push_global(L, "mousemoverel", Env::Input::mousemoverel);
	push_global(L, "mousescroll", Env::Input::mousescroll);

	lua_newtable(L);
	push_member(L, "invalidate", Env::Cache::invalidate);
	push_member(L, "iscached", Env::Cache::iscached);
	push_member(L, "replace", Env::Cache::replace);
	lua_setfield(L, LUA_GLOBALSINDEX, ("cache"));

	push_global(L, "cloneref", Env::Cache::cloneref);
	push_global(L, "compareinstances", Env::Cache::compareinstances);

	push_global(L, "getrawmetatable", Env::Metatable::getrawmetatable);
	push_global(L, "setnamecallmethod", Env::Metatable::setnamecallmethod);
	push_global(L, "isreadonly", Env::Metatable::isreadonly);
	push_global(L, "setrawmetatable", Env::Metatable::setrawmetatable);
	push_global(L, "setreadonly", Env::Metatable::setreadonly);
	push_global(L, ("makereadonly"), Env::Metatable::make_readonly);
	push_global(L, ("makewritable"), Env::Metatable::make_writable);

	push_global(L, "base64_encode", Env::Crypt::base64encode);
	push_global(L, "base64_decode", Env::Crypt::base64decode);

	lua_newtable(L);
	push_member(L, ("encode"), Env::Crypt::base64encode);
	push_member(L, ("decode"), Env::Crypt::base64decode);
	lua_setfield(L, LUA_GLOBALSINDEX, ("base64"));

	lua_newtable(L);
	push_member(L, ("base64encode"), Env::Crypt::base64encode);
	push_member(L, ("base64decode"), Env::Crypt::base64decode);
	push_member(L, ("base64_encode"), Env::Crypt::base64encode);
	push_member(L, ("base64_decode"), Env::Crypt::base64decode);

	lua_newtable(L);
	push_member(L, ("encode"), Env::Crypt::base64encode);
	push_member(L, ("decode"), Env::Crypt::base64decode);
	lua_setfield(L, -2, ("base64"));

	push_member(L, ("encrypt"), Env::Crypt::encrypt);
	push_member(L, ("decrypt"), Env::Crypt::decrypt);
	push_member(L, ("generatebytes"), Env::Crypt::generatebytes);
	push_member(L, ("generatekey"), Env::Crypt::generatekey);
	push_member(L, ("hash"), Env::Crypt::hash);

	lua_setfield(L, LUA_GLOBALSINDEX, ("crypt"));

	push_global(L, "encrypt", Env::Crypt::encrypt);
	push_global(L, "decrypt", Env::Crypt::decrypt);
	push_global(L, "generatebytes", Env::Crypt::generatebytes);
	push_global(L, "generatekey", Env::Crypt::generatekey);
	push_global(L, "hash", Env::Crypt::hash);
	push_global(L, "base64encode", Env::Crypt::base64encode);
	push_global(L, "base64decode", Env::Crypt::base64decode);

	lua_newtable(L);
	push_member(L, ("getregistry"), Env::Scripts::getreg);
	push_member(L, ("getupvalue"), Env::Debug::debug_getupvalue);
	push_member(L, ("getupvalues"), Env::Debug::debug_getupvalues);
	push_member(L, ("setupvalue"), Env::Debug::debug_setupvalue);
	push_member(L, ("getconstant"), Env::Debug::debug_getconstant);
	push_member(L, ("getconstants"), Env::Debug::debug_getconstants);
	push_member(L, ("setconstant"), Env::Debug::debug_setconstant);
	push_member(L, ("getinfo"), Env::Debug::debug_getinfo);
	push_member(L, ("getstack"), Env::Debug::debug_getstack);
	push_member(L, ("setstack"), Env::Debug::debug_setstack);
	push_member(L, ("getproto"), Env::Debug::debug_getproto);
	push_member(L, ("getprotos"), Env::Debug::debug_getprotos);
	lua_setfield(L, LUA_GLOBALSINDEX, ("debug"));

	push_global(L, ("getregistry"), Env::Scripts::getreg);
	push_global(L, ("getupvalue"), Env::Debug::debug_getupvalue);
	push_global(L, ("getupvalues"), Env::Debug::debug_getupvalues);
	push_global(L, ("setupvalue"), Env::Debug::debug_setupvalue);
	push_global(L, ("getconstant"), Env::Debug::debug_getconstant);
	push_global(L, ("getconstants"), Env::Debug::debug_getconstants);
	push_global(L, ("setconstant"), Env::Debug::debug_setconstant);
	push_global(L, ("getinfo"), Env::Debug::debug_getinfo);
	push_global(L, ("getstack"), Env::Debug::debug_getstack);
	push_global(L, ("setstack"), Env::Debug::debug_setstack);
	push_global(L, ("getproto"), Env::Debug::debug_getproto);
	push_global(L, ("getprotos"), Env::Debug::debug_getprotos);


	lua_newtable(L);
	push_member(L, ("connect"), Env::WebSocket::websocket_connect);
	push_member(L, ("Connect"), Env::WebSocket::websocket_connect);
	push_member(L, ("new"), Env::WebSocket::websocket_connect);
	push_member(L, ("New"), Env::WebSocket::websocket_connect);
	lua_setfield(L, LUA_GLOBALSINDEX, ("WebSocket"));

	push_global(L, ("gethui"), Env::Scripts::gethui);
	push_global(L, ("setclipboard"), Env::Scripts::setclipboard);
	push_global(L, ("toclipboard"), Env::Scripts::setclipboard);
	push_global(L, ("write_clipboard"), Env::Scripts::setclipboard);
	push_global(L, ("httpget"), Env::HTTP::httpget);
	push_global(L, ("getobjects"), Env::Scripts::getobjects);
	push_global(L, ("identifyexecutor"), Env::Scripts::identifyexecutor);
	push_global(L, ("getexecutorname"), Env::Scripts::identifyexecutor);
	push_global(L, ("request"), Env::HTTP::request);
	push_global(L, ("http_request"), Env::HTTP::request);
	push_global(L, ("queue_on_teleport"), Env::Scripts::queue_on_teleport);
	push_global(L, ("queueonteleport"), Env::Scripts::queue_on_teleport);

	lua_newtable(L);
	push_member(L, ("request"), Env::HTTP::request);
	lua_setfield(L, LUA_GLOBALSINDEX, ("http"));

	push_global(L, ("setfps"), Env::Scripts::setfps);
	push_global(L, ("set_fps"), Env::Scripts::setfps);
	push_global(L, ("setfpscap"), Env::Scripts::setfps);
	push_global(L, ("set_fps_cap"), Env::Scripts::setfps);

	push_global(L, ("getfps"), Env::Scripts::getfps);
	push_global(L, ("get_fps"), Env::Scripts::getfps);
	push_global(L, ("getfpscap"), Env::Scripts::getfps);
	push_global(L, ("get_fps_cap"), Env::Scripts::getfps);

	push_global(L, ("getsenv"), Env::Scripts::getsenv);
	push_global(L, ("getloadedmodules"), Env::Scripts::getloadedmodules1);
	push_global(L, ("getmenv"), Env::Scripts::getsenv);

	push_global(L, ("getrunningscripts"), Env::Scripts::getrunningscripts);
	push_global(L, ("getscriptswiththreads"), Env::Scripts::getrunningscripts);

	push_global(L, ("firetouchinterest"), Env::Scripts::firetouchinterest);
	push_global(L, ("fireclickdetector"), Env::Scripts::fireclickdetector);

	push_global(L, ("gethwid"), Env::Instance::gethwid);
	push_global(L, ("isluau"), Env::Instance::isluau);
	push_global(L, ("getinstancelist"), Env::Instance::getinstancelist);
	push_global(L, ("getinstances"), Env::Instance::getinstances);
	push_global(L, ("getnilinstances"), Env::Instance::getnilinstances);
	push_global(L, ("get_instances"), Env::Instance::getinstances);
	push_global(L, ("get_nil_instances"), Env::Instance::getnilinstances);
	push_global(L, ("GetInstances"), Env::Instance::getinstances);
	push_global(L, ("GetNilInstances"), Env::Instance::getnilinstances);

	push_global(L, "getscriptbytecode", Env::Scripts::getscriptbytecode);
	push_global(L, "dumpstring", Env::Scripts::getscriptbytecode);

	push_global(L, "getcallbackvalue", Env::Scripts::getcallbackvalue);

	push_global(L, ("gethiddenproperty"), Env::Instance::gethiddenproperty);
	push_global(L, ("sethiddenproperty"), Env::Instance::sethiddenproperty);
	push_global(L, ("isscriptable"), Env::Instance::isscriptable);
	push_global(L, ("setscriptable"), Env::Instance::setscriptable);

	push_global(L, "getidentity", Env::Scripts::getidentity);
	push_global(L, "getthreadidentity", Env::Scripts::getidentity);
	push_global(L, "getthreadcontext", Env::Scripts::getidentity);
	push_global(L, "getcontext", Env::Scripts::getidentity);

	push_global(L, "setthreadidentity", Env::Scripts::setidentity);
	push_global(L, "setthreadcontext", Env::Scripts::setidentity);
	push_global(L, "setidentity", Env::Scripts::setidentity);

	push_global(L, ("getscripts"), Env::Instance::getscripts);
	push_global(L, ("getscriptclosure"), Env::Scripts::getscriptclosure);

	push_global(L, "lz4compress", Env::Scripts::lz4compress);
	push_global(L, "lz4decompress", Env::Scripts::lz4decompress);

	push_global(L, ("getscripthash"), Env::Scripts::getscripthash);

	push_global(L, ("fireproximityprompt"), Env::Scripts::fireproximityprompt);

	push_global(L, ("httpget"), Env::HTTP::httpget);
	push_global(L, ("getobjects"), Env::Scripts::getobjects);
	push_global(L, ("request"), Env::HTTP::request);
	push_global(L, ("http_request"), Env::HTTP::request);
	push_global(L, ("loadstring"), Env::Closures::loadstring);
	push_global(L, ("load"), Env::Closures::loadstring);

	Env::Filesystem::HelpFunctions::Init();
	push_global(L, "appendfile", Env::Filesystem::appendfile);
	push_global(L, "readfile", Env::Filesystem::readfile);
	push_global(L, "listfiles", Env::Filesystem::listfiles);
	push_global(L, "writefile", Env::Filesystem::writefile);
	push_global(L, "makefolder", Env::Filesystem::makefolder);
	push_global(L, "isfile", Env::Filesystem::isfile);
	push_global(L, "isfolder", Env::Filesystem::isfolder);
	push_global(L, "delfile", Env::Filesystem::delfile);
	push_global(L, "delfolder", Env::Filesystem::delfolder);
	push_global(L, "loadfile", Env::Filesystem::loadfile);
	push_global(L, "getcustomasset", Env::Filesystem::getcustomasset);

	push_global(L, "hookmetamethod", Env::Closures::hookmetamethod);
	push_global(L, "getnamecallmethod", Env::Metatable::getnamecallmethod);

	push_global(L, ("getcallingscript"), Env::Scripts::getcallingscript);
	push_global(L, ("get_calling_script"), Env::Scripts::getcallingscript);
	push_global(L, ("getcurrentscript"), Env::Scripts::getcallingscript);

	push_global(L, ("newcclosure"), Env::Closures::newcclosure);
	push_global(L, ("new_c_closure"), Env::Closures::newcclosure);

	lua_newtable(L);
	push_member(L, oxorany("band"), Bit::bit_band);
	push_member(L, oxorany("bor"), Bit::bit_bor);
	push_member(L, oxorany("bxor"), Bit::bit_bxor);
	push_member(L, oxorany("bnot"), Bit::bit_bnot);
	push_member(L, oxorany("lshift"), Bit::bit_lshift);
	push_member(L, oxorany("rshift"), Bit::bit_rshift);
	push_member(L, oxorany("rol"), Bit::bit_rol);
	push_member(L, oxorany("ror"), Bit::bit_ror);
	push_member(L, oxorany("blshift"), Bit::bit_blshift);
	push_member(L, oxorany("brshift"), Bit::bit_brshift);
	push_member(L, oxorany("bmul"), Bit::bit_bmul);
	push_member(L, oxorany("bswap"), Bit::bit_bswap);
	push_member(L, oxorany("bdiv"), Bit::bit_bdiv);
	push_member(L, oxorany("badd"), Bit::bit_badd);
	push_member(L, oxorany("bsub"), Bit::bit_bsub);
	lua_setfield(L, LUA_GLOBALSINDEX, ("bit"));

	push_global(L, "isparallel", Actors::isparallel);
	push_global(L, "getactors", Actors::getactors);

	push_global(L, "getproperties", Properties::getproperties);
	push_global(L, "gethiddenproperties", Properties::gethiddenproperties);

	push_global(L, "getfunctionbytecode", Env::Scripts::getfunctionbytecode);
	push_global(L, "getfunctionhash", Env::Scripts::getfunctionbytecode);
	MetaHooks::initialize(L);
	Sleep(1);
	rcv::defs::Print(0, "Env is loaded!");
}