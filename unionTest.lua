require 'runtime'

local IsLs

local Ls
local IsNil

local Nil
local Array

local IsArray
local base
local insert
local res
local sres
local len
local ins
local concatList
local xs
local compose2
local __new_lifted_lambda_0
local __new_lifted_lambda_1
local lenApply
local lenApplied


function Ls(x1, x2) return { _type = "Ls", _args = {x1, x2}, r = x1, res = x2} end
IsNil = function(a) return IsStruct({structSpec = {}})(a) end
function Array(x1) return { _type = "Array", _args = {x1}, _value = x1} end
base = function()
	
	return {}
end
insert = function(arr, a)
	
	return concat(arr, Array(a))
end
res = Array(1)
res = insert(insert(res, true), "mooo")
res = concat(res, Array({p = true}))
sres = insert(res, {b = "Hello"})
sres = concat(sres, Array({a = 3}))
res = concat(res, Array(sres))
println(res)
local len
len = function(xs)
	
	if not IsType(xs, function(a) return IsNamedType({namedTypeSpec = {name = "Ls", args = {function(a) return AnyMatching({constraintSpec = {}})(a) end}}})(a) end) then
		
		return 0
	else
		
		return add(len(xs.res), 1)
	end
end
ins = function(a, ls)
	
	return Ls(a, ls)
end
concatList = function(as, bs)
	
	if IsType(as, function(a) return IsNil(a) end) then
		
		return bs
	else
		
		return Ls(as.r, concatList(as.res, bs))
	end
end
xs = ins(true, ins(1, Ls("ddjn", {})))
xs = ins("ok", xs)
xs = concatList(Ls({x = 8}, {}), xs)
println(len(xs))
compose2 = function(g, f)
	local __new_lifted_lambda_1
	
	
	__new_lifted_lambda_1 = function(x)
		
		return g(f(x))
	end
	return __new_lifted_lambda_1
end
__new_lifted_lambda_0 = function(a)
	
	
	a.length = mul(a.length, 2)
	return a
end
__new_lifted_lambda_1 = function(ls)
	
	return {length = len(ls), list = ls}
end
lenApply = compose2(__new_lifted_lambda_0, __new_lifted_lambda_1)
lenApplied = lenApply(xs)
println(lenApplied)
if not IsType(res, function(a) return IsNil(a) end) then
	local x
	
	
	x = index(res, 3)
	if IsType(x, function(a) return IsString(a) end) then
		
		println(add(x, "hoo"))
	else
		
		if IsType(x, function(a) return IsInt(a) end) then
			
			println(add(x, 1))
		else
			
			println(x)
		end
	end
else

end