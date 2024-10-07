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
									if (Enum == 0) then
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								elseif (Enum == 2) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 6) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum > 7) then
								Stk[Inst[2]] = {};
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 12) then
							if (Enum <= 10) then
								if (Enum > 9) then
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
										if (Mvm[1] == 51) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum > 11) then
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
						elseif (Enum <= 14) then
							if (Enum > 13) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 15) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 16) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						else
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						end
					elseif (Enum <= 26) then
						if (Enum <= 21) then
							if (Enum <= 19) then
								if (Enum > 18) then
									do
										return;
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
							elseif (Enum == 20) then
								Stk[Inst[2]] = Inst[3];
							else
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 23) then
							if (Enum > 22) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum <= 24) then
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						elseif (Enum > 25) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						end
					elseif (Enum <= 31) then
						if (Enum <= 28) then
							if (Enum > 27) then
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
						elseif (Enum <= 29) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 30) then
							Stk[Inst[2]] = Inst[3] ~= 0;
						else
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						end
					elseif (Enum <= 33) then
						if (Enum == 32) then
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
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 34) then
						Stk[Inst[2]] = Stk[Inst[3]];
					elseif (Enum > 35) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 54) then
					if (Enum <= 45) then
						if (Enum <= 40) then
							if (Enum <= 38) then
								if (Enum == 37) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									local A = Inst[2];
									do
										return Unpack(Stk, A, A + Inst[3]);
									end
								end
							elseif (Enum > 39) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 42) then
							if (Enum > 41) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 43) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 44) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 49) then
						if (Enum <= 47) then
							if (Enum == 46) then
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							end
						elseif (Enum == 48) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
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
					elseif (Enum <= 51) then
						if (Enum == 50) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 52) then
						VIP = Inst[3];
					elseif (Enum == 53) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 63) then
					if (Enum <= 58) then
						if (Enum <= 56) then
							if (Enum > 55) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								do
									return;
								end
							end
						elseif (Enum > 57) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 60) then
						if (Enum == 59) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 61) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum == 62) then
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
					else
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
							if (Mvm[1] == 51) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					end
				elseif (Enum <= 68) then
					if (Enum <= 65) then
						if (Enum == 64) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 66) then
						Stk[Inst[2]] = Inst[3] ~= 0;
					elseif (Enum == 67) then
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
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
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 71) then
					local A = Inst[2];
					do
						return Unpack(Stk, A, Top);
					end
				elseif (Enum == 72) then
					Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
				else
					local A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Top));
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!493Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403063Q00E4D0DE37CFBF03083Q007EB1A3BB4586DBA7022Q00E0BE88D9FA4103083Q0016DE2FD7F222C02F03053Q009C43AD4AA503113Q0023B65A05BD284924A25A19AC275431B31A03073Q002654D72976DC4603063Q0065052700D75403053Q009E30764272022Q00207C8718E94103083Q009E3715247DA4F6AE03073Q009BCB44705613C5030A3Q0062D820F54C2FB4AA168E03083Q009826BD569C20188503063Q00C944A254D55303043Q00269C37C7022Q0020F8ECB0F44103083Q009D6E793A1D75F74603083Q0023C81D1C4873149A030F3Q003CADD8DC867D664AEB84CE9C3D250803073Q005479DFB1BFED4C03063Q008E45CCB2135403083Q00A1DB36A9C05A3050022Q0070F48F12F14103083Q007C51053747430D2003043Q004529226003083Q0090E8CF100E22BFCC03063Q004BDCA3B76A6203063Q0037A98E25F00603053Q00B962DAEB57023Q000B6FCEF14103083Q00FE2F22F4D0ABC63903063Q00CAAB5C4786BE030B3Q001DF11FB705F41AA90EE47B03043Q00E849A14C03063Q008ECA474F37BF03053Q007EDBB9223D023Q00FA3A62E64103083Q0039DD5B607076FEE203083Q00876CAE3E121E179303083Q009ACE04EE2D9A01E803083Q00A7D6894AAB78CE5303063Q00BEE3374FD1A303063Q00C7EB90523D98023Q00AAA366E54103083Q003205BC390917B42E03043Q004B6776D903103Q00C65A641BB717C8052247ED4B9103642Q03063Q007EA7341074D903063Q00FD3D25929D1D03073Q009CA84E40E0D479022Q00404ABA69E74103083Q0032FDA0DC09EFA8CB03043Q00AE678EC5030A3Q007B016C190072CA72700F03073Q009836483F58453E03043Q0067616D6503073Q00506C6179657273030B3Q004C6F63616C506C6179657203063Q0055736572496403043Q004E616D6503043Q004B69636B032D3Q004E6F20657374C383C2A173206175746F72697A61646F207061726120757361722065737465207363726970742E00A23Q0012233Q00013Q00202B5Q0002001223000100013Q00202B000100010003001223000200013Q00202B000200020004001223000300053Q00063B0003000A000100010004273Q000A0001001223000300063Q00202B000400030007001223000500083Q00202B000500050009001223000600083Q00202B00060006000A00060A00073Q000100062Q00333Q00064Q00338Q00333Q00044Q00333Q00014Q00333Q00024Q00333Q00054Q0041000800084Q004100093Q00022Q0022000A00073Q001215000B000B3Q001215000C000C4Q000F000A000C00020020030009000A000D2Q0022000A00073Q001215000B000E3Q001215000C000F4Q000F000A000C00022Q0022000B00073Q001215000C00103Q001215000D00114Q000F000B000D00022Q00300009000A000B2Q0041000A3Q00022Q0022000B00073Q001215000C00123Q001215000D00134Q000F000B000D0002002003000A000B00142Q0022000B00073Q001215000C00153Q001215000D00164Q000F000B000D00022Q0022000C00073Q001215000D00173Q001215000E00184Q000F000C000E00022Q0030000A000B000C2Q0041000B3Q00022Q0022000C00073Q001215000D00193Q001215000E001A4Q000F000C000E0002002003000B000C001B2Q0022000C00073Q001215000D001C3Q001215000E001D4Q000F000C000E00022Q0022000D00073Q001215000E001E3Q001215000F001F4Q000F000D000F00022Q0030000B000C000D2Q0041000C3Q00022Q0022000D00073Q001215000E00203Q001215000F00214Q000F000D000F0002002003000C000D00222Q0022000D00073Q001215000E00233Q001215000F00244Q000F000D000F00022Q0022000E00073Q001215000F00253Q001215001000264Q000F000E001000022Q0030000C000D000E2Q0041000D3Q00022Q0022000E00073Q001215000F00273Q001215001000284Q000F000E00100002002003000D000E00292Q0022000E00073Q001215000F002A3Q0012150010002B4Q000F000E001000022Q0022000F00073Q0012150010002C3Q0012150011002D4Q000F000F001100022Q0030000D000E000F2Q0041000E3Q00022Q0022000F00073Q0012150010002E3Q0012150011002F4Q000F000F00110002002003000E000F00302Q0022000F00073Q001215001000313Q001215001100324Q000F000F001100022Q0022001000073Q001215001100333Q001215001200344Q000F0010001200022Q0030000E000F00102Q0041000F3Q00022Q0022001000073Q001215001100353Q001215001200364Q000F001000120002002003000F001000372Q0022001000073Q001215001100383Q001215001200394Q000F0010001200022Q0022001100073Q0012150012003A3Q0012150013003B4Q000F0011001300022Q0030000F001000112Q004100103Q00022Q0022001100073Q0012150012003C3Q0012150013003D4Q000F00110013000200200300100011003E2Q0022001100073Q0012150012003F3Q001215001300404Q000F0011001300022Q0022001200073Q001215001300413Q001215001400424Q000F0012001400022Q00300010001100122Q001000080008000100060A00090001000100012Q00333Q00083Q001223000A00433Q00202B000A000A004400202B000A000A004500202B000B000A004600202B000C000A00472Q0022000D00094Q0022000E000B4Q0022000F000C4Q000F000D000F000200063B000D00A1000100010004273Q00A10001002007000D000A0048001215000F00494Q003A000D000F00012Q00373Q00014Q00373Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q004100025Q001215000300014Q001600045Q001215000500013Q00041B0003002100012Q001700076Q0022000800024Q0017000900014Q0017000A00024Q0017000B00034Q0017000C00044Q0022000D6Q0022000E00063Q00201E000F000600012Q0002000C000F4Q0005000B3Q00022Q0017000C00034Q0017000D00044Q0022000E00014Q0016000F00014Q002F000F0006000F001018000F0001000F2Q0016001000014Q002F00100006001000101800100001001000201E0010001000012Q0002000D00104Q0035000C6Q0005000A3Q000200200E000A000A00022Q00060009000A4Q004900073Q00010004200003000500012Q0017000300054Q0022000400024Q003C000300044Q004700036Q00373Q00017Q00033Q0003063Q0069706169727303063Q0055736572496403083Q00557365726E616D6502113Q001223000200014Q001700036Q00240002000200040004273Q000C000100202B00070006000200061D0007000A00013Q0004273Q000A000100202B0007000600030006360007000C000100010004273Q000C00012Q001F000700014Q000D000700023Q00063E00020004000100020004273Q000400012Q001F00026Q000D000200024Q00373Q00017Q00", GetFEnv(), ...);
