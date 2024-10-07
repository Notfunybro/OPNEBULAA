--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.8) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 36) then
					if (Enum <= 17) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum > 0) then
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									else
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									end
								elseif (Enum == 2) then
									Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
								elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 6) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							elseif (Enum == 7) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								do
									return;
								end
							end
						elseif (Enum <= 12) then
							if (Enum <= 10) then
								if (Enum == 9) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum > 11) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 14) then
							if (Enum > 13) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 15) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum > 16) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 26) then
						if (Enum <= 21) then
							if (Enum <= 19) then
								if (Enum > 18) then
									local NewProto = Proto[Inst[3]];
									local NewUvals;
									local Indexes = {};
									NewUvals = Setmetatable({}, {__index=function(_, Key)
										local Val = Indexes[Key];
										return Val[1][Val[2]];
									end,__newindex=function(_, Key, Value)
										local Val = Indexes[Key];
										Val[1][Val[2]] = Value;
									end});
									for Idx = 1, Inst[4] do
										VIP = VIP + 1;
										local Mvm = Instr[VIP];
										if (Mvm[1] == 47) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								end
							elseif (Enum == 20) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 23) then
							if (Enum == 22) then
								Stk[Inst[2]] = {};
							else
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							end
						elseif (Enum <= 24) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum == 25) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 31) then
						if (Enum <= 28) then
							if (Enum > 27) then
								VIP = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 29) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 30) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 33) then
						if (Enum == 32) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 34) then
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					elseif (Enum > 35) then
						local NewProto = Proto[Inst[3]];
						local NewUvals;
						local Indexes = {};
						NewUvals = Setmetatable({}, {__index=function(_, Key)
							local Val = Indexes[Key];
							return Val[1][Val[2]];
						end,__newindex=function(_, Key, Value)
							local Val = Indexes[Key];
							Val[1][Val[2]] = Value;
						end});
						for Idx = 1, Inst[4] do
							VIP = VIP + 1;
							local Mvm = Instr[VIP];
							if (Mvm[1] == 47) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
				elseif (Enum <= 54) then
					if (Enum <= 45) then
						if (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum == 37) then
									do
										return;
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum == 39) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 42) then
							if (Enum > 41) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum <= 43) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 44) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 49) then
						if (Enum <= 47) then
							if (Enum > 46) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum == 48) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 51) then
						if (Enum == 50) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 52) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					elseif (Enum > 53) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 63) then
					if (Enum <= 58) then
						if (Enum <= 56) then
							if (Enum == 55) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								VIP = Inst[3];
							end
						elseif (Enum > 57) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 60) then
						if (Enum > 59) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 61) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					elseif (Enum > 62) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					else
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 68) then
					if (Enum <= 65) then
						if (Enum > 64) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 66) then
						local A = Inst[2];
						local T = Stk[A];
						for Idx = A + 1, Inst[3] do
							Insert(T, Stk[Idx]);
						end
					elseif (Enum == 67) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 70) then
					if (Enum > 69) then
						local A = Inst[2];
						local T = Stk[A];
						local B = Inst[3];
						for Idx = 1, B do
							T[Idx] = Stk[A + Idx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					end
				elseif (Enum <= 71) then
					Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
				elseif (Enum == 72) then
					Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
				else
					local A = Inst[2];
					Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!503Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403063Q00E4D0DE37CFBF03083Q007EB1A3BB4586DBA7022Q00E0BE88D9FA4103083Q0016DE2FD7F222C02F03053Q009C43AD4AA503113Q0023B65A05BD284924A25A19AC275431B31A03073Q002654D72976DC4603063Q0065052700D75403053Q009E30764272022Q00207C8718E94103083Q009E3715247DA4F6AE03073Q009BCB44705613C5030A3Q0062D820F54C2FB4AA168E03083Q009826BD569C20188503063Q00C944A254D55303043Q00269C37C7022Q0020F8ECB0F44103083Q009D6E793A1D75F74603083Q0023C81D1C4873149A030F3Q003CADD8DC867D664AEB84CE9C3D250803073Q005479DFB1BFED4C03063Q008E45CCB2135403083Q00A1DB36A9C05A3050022Q0070F48F12F14103083Q007C51053747430D2003043Q004529226003083Q0090E8CF100E22BFCC03063Q004BDCA3B76A6203063Q0037A98E25F00603053Q00B962DAEB57023Q000B6FCEF14103083Q00FE2F22F4D0ABC63903063Q00CAAB5C4786BE030B3Q001DF11FB705F41AA90EE47B03043Q00E849A14C03063Q008ECA474F37BF03053Q007EDBB9223D023Q00FA3A62E64103083Q0039DD5B607076FEE203083Q00876CAE3E121E179303083Q009ACE04EE2D9A01E803083Q00A7D6894AAB78CE5303063Q00BEE3374FD1A303063Q00C7EB90523D98023Q00AAA366E54103083Q003205BC390917B42E03043Q004B6776D903103Q00C65A641BB717C8052247ED4B9103642Q03063Q007EA7341074D903063Q00FD3D25929D1D03073Q009CA84E40E0D479022Q00404ABA69E74103083Q0032FDA0DC09EFA8CB03043Q00AE678EC5030A3Q007B016C190072CA72700F03073Q009836483F58453E03063Q00E1D7EB4EFDC003043Q003CB4A48E022Q00A0BC39D2EB4103083Q006D4D003B29EC1F5D03073Q0072383E6549478D030B3Q00B2E6C8C1A8E2C3C0E9BB8903043Q00A4D889BB03043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203063Q0055736572496403043Q004E616D6503043Q004B69636B032B3Q004E6F20657374C3A173206175746F72697A61646F207061726120757361722065737465207363726970742E00B13Q0012443Q00013Q00200F5Q0002001244000100013Q00200F000100010003001244000200013Q00200F000200020004001244000300053Q0006410003000A0001000100041C3Q000A0001001244000300063Q00200F000400030007001244000500083Q00200F000500050009001244000600083Q00200F00060006000A00062400073Q000100062Q002F3Q00064Q002F8Q002F3Q00044Q002F3Q00014Q002F3Q00024Q002F3Q00054Q0035000800094Q003500093Q00022Q000C000A00073Q001214000B000B3Q001214000C000C4Q0023000A000C00020020320009000A000D2Q000C000A00073Q001214000B000E3Q001214000C000F4Q0023000A000C00022Q000C000B00073Q001214000C00103Q001214000D00114Q0023000B000D00022Q00200009000A000B2Q0035000A3Q00022Q000C000B00073Q001214000C00123Q001214000D00134Q0023000B000D0002002032000A000B00142Q000C000B00073Q001214000C00153Q001214000D00164Q0023000B000D00022Q000C000C00073Q001214000D00173Q001214000E00184Q0023000C000E00022Q0020000A000B000C2Q0035000B3Q00022Q000C000C00073Q001214000D00193Q001214000E001A4Q0023000C000E0002002032000B000C001B2Q000C000C00073Q001214000D001C3Q001214000E001D4Q0023000C000E00022Q000C000D00073Q001214000E001E3Q001214000F001F4Q0023000D000F00022Q0020000B000C000D2Q0035000C3Q00022Q000C000D00073Q001214000E00203Q001214000F00214Q0023000D000F0002002032000C000D00222Q000C000D00073Q001214000E00233Q001214000F00244Q0023000D000F00022Q000C000E00073Q001214000F00253Q001214001000264Q0023000E001000022Q0020000C000D000E2Q0035000D3Q00022Q000C000E00073Q001214000F00273Q001214001000284Q0023000E00100002002032000D000E00292Q000C000E00073Q001214000F002A3Q0012140010002B4Q0023000E001000022Q000C000F00073Q0012140010002C3Q0012140011002D4Q0023000F001100022Q0020000D000E000F2Q0035000E3Q00022Q000C000F00073Q0012140010002E3Q0012140011002F4Q0023000F00110002002032000E000F00302Q000C000F00073Q001214001000313Q001214001100324Q0023000F001100022Q000C001000073Q001214001100333Q001214001200344Q00230010001200022Q0020000E000F00102Q0035000F3Q00022Q000C001000073Q001214001100353Q001214001200364Q0023001000120002002032000F001000372Q000C001000073Q001214001100383Q001214001200394Q00230010001200022Q000C001100073Q0012140012003A3Q0012140013003B4Q00230011001300022Q0020000F001000112Q003500103Q00022Q000C001100073Q0012140012003C3Q0012140013003D4Q002300110013000200203200100011003E2Q000C001100073Q0012140012003F3Q001214001300404Q00230011001300022Q000C001200073Q001214001300413Q001214001400424Q00230012001400022Q00200010001100122Q003500113Q00022Q000C001200073Q001214001300433Q001214001400444Q00230012001400020020320011001200452Q000C001200073Q001214001300463Q001214001400474Q00230012001400022Q000C001300073Q001214001400483Q001214001500494Q00230013001500022Q00200011001200132Q000100080009000100062400090001000100012Q002F3Q00083Q001244000A004A3Q00200F000A000A004B00200F000A000A004C00200F000B000A004D00200F000C000A004E2Q000C000D00094Q000C000E000B4Q000C000F000C4Q0023000D000F0002000641000D00B00001000100041C3Q00B00001002033000D000A004F001214000F00504Q001D000D000F00012Q00253Q00014Q00253Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q003500025Q001214000300014Q000E00045Q001214000500013Q0004170003002100012Q002B00076Q000C000800024Q002B000900014Q002B000A00024Q002B000B00034Q002B000C00044Q000C000D6Q000C000E00063Q00200B000F000600012Q0018000C000F4Q003B000B3Q00022Q002B000C00034Q002B000D00044Q000C000E00014Q000E000F00014Q0047000F0006000F001048000F0001000F2Q000E001000014Q004700100006001000104800100001001000200B0010001000012Q0018000D00104Q001A000C6Q003B000A3Q0002002045000A000A00022Q002E0009000A4Q001000073Q00010004120003000500012Q002B000300054Q000C000400024Q002C000300044Q003400036Q00253Q00017Q00033Q0003063Q0069706169727303063Q0055736572496403083Q00557365726E616D6502113Q001244000200014Q002B00036Q000A00020002000400041C3Q000C000100200F0007000600020006370007000A00013Q00041C3Q000A000100200F0007000600030006270007000C0001000100041C3Q000C00012Q003A000700014Q0031000700023Q000640000200040001000200041C3Q000400012Q003A00026Q0031000200024Q00253Q00017Q00", GetFEnv(), ...);
