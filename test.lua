require 'runtime'

local IsPet

local Pet
local IsMoo

local Moo
local IsPerson

local Person
local Date

local IsDate
local IsNil

local Nil
local IsTup

local Tup
local s
local x
local b
local i
local fl
local go
local mutu1
local mutu2
local apply
local given
local __new_lifted_lambda_0
local application
local changeCatName
local modifyAge
local st
local nm1
local ag1
local setName
local sn
local fi
local fires
local fn
local swapG
local swapML
local btool
local mlres
local identity
local fst
local snd
local tres
local idresf
local idres
local ftr
local flr
local basicPerson


IsPet = function(a) return IsStruct({structSpec = {color = function(a) return IsString(a) end, name = function(a) return IsString(a) end, species = function(a) return IsString(a) end}})(a) end
IsMoo = function(a) return IsStruct({structSpec = {age = function(a) return IsInt(a) end, male = function(a) return IsBool(a) end, name = function(a) return IsString(a) end, pet = function(a) return IsPet(a) end}})(a) end
IsPerson = function(a) return IsStruct({structSpec = {age = function(a) return IsInt(a) end, male = function(a) return IsBool(a) end, name = function(a) return IsString(a) end, parent = function(a) return Choice({function(a) return IsNil(a) end, function(a) return IsPerson(a) end})(a) end, pet = function(a) return IsPet(a) end}})(a) end
IsDate = function(a) return IsStruct({structSpec = {month = function(a) return IsInt(a) end, weekday = function(a) return IsInt(a) end, year = function(a) return IsInt(a) end}})(a) end
IsNil = function(a) return IsStruct({structSpec = {}})(a) end
function Tup(x1, x2) return { _type = "Tup", _args = {x1, x2}, a = x1, b = x2} end
println("\n\n\nProgram begins: \n")
local s = Tup(1, true)
local x = s.a
local b = s.b
x = 4
local i = 0
local fl = function(a, b)
	local __new_lifted_lambda_1
	
	
	local __new_lifted_lambda_1 = function(n)
		local __new_lifted_lambda_2
		
		
		local __new_lifted_lambda_2 = function(h)
			local __new_lifted_lambda_3
			
			
			local __new_lifted_lambda_3 = function()
				
				return h.name
			end
			return __new_lifted_lambda_3
		end
		return __new_lifted_lambda_2
	end
	return __new_lifted_lambda_1
end
local go = function(a, b)
	local f
	
	local ans
	
	
	local f = function(n)
		local zoo
		
		
		local zoo = mul(n, 3)
		return n
	end
	local ans = add(a, b)
	return f(ans)
end
local mutu1
local mutu2
mutu1 = function(a, b)
	
	return mutu2(b, true)
end
mutu2 = function(n, a)
	
	if b then
		
		return 1
	else
		
		return mutu1(n, add(n, 1))
	end
end
local apply = function(f, x)
	
	return f(x)
end
local given = fl(1, true)(true)({color = "Black", name = "Hello's kitty", species = "Cat"})()
local __new_lifted_lambda_0 = function(a)
	
	return eq(a, 1)
end
local application = apply(__new_lifted_lambda_0, 1)
local changeCatName = function(person, name)
	local f
	
	
	local f = function()
		
		if lt(person.age, 5) then
			local catties
			
			
			
			
			local catties = 1
			catties = add(catties, 1)
			person.pet.name = person.name
			return person.pet.name
		else
			
			if lt(person.age, 100) then
				
				
				person.pet.name = name
				return person.pet.name
			else
				
				return "Dead man's cat"
			end
		end
	end
	return f()
end
local modifyAge = function(person, age)
	
	
	person.age = lt(age, 0) and 0 or age
	return age
end
local st = {age = 10, male = true, name = "Ameer", parent = {}, pet = {color = "White", name = "Tom", species = "Cat"}}
st.parent = duplicate(st)
local nm1 = changeCatName(st, "Molly")
local ag1 = modifyAge(st, add(st.age, 1))
write("st is: ")
println(st)
setName = newOpenFunction()
newOpenInstance(setName, function(s, area, person) return IsType(s, function(a) return IsString(a) end) and IsType(area, function(a) return IsString(a) end) and IsType(person, function(a) return IsPerson(a) end) end, function(s, area, person)
	person.name = s
	return person.pet
end)
newOpenInstance(setName, function(s, area, cat) return IsType(s, function(a) return IsString(a) end) and IsType(area, function(a) return IsString(a) end) and IsType(cat, function(a) return IsStruct({structSpec = {pet = function(a) return IsPerson(a) end}})(a) end) end, function(s, area, cat)
	cat.pet.name = s
	return cat.pet
end)
newOpenInstance(setName, function(i, area, intkeeper) return IsType(i, function(a) return IsInt(a) end) and IsType(area, function(a) return IsString(a) end) and IsType(intkeeper, function(a) return IsStruct({structSpec = {pet = function(a) return IsStruct({structSpec = {name = function(a) return IsInt(a) end}})(a) end}})(a) end) end, function(i, area, intkeeper)
	intkeeper.pet.name = i
	return intkeeper.pet
end)
local sn = setName("Junu", "Collatz", {pet = st})
write("sn is: ")
println(sn)
fi = newOpenFunction()
newOpenInstance(fi, function(i) return IsType(i, function(a) return IsInt(a) end) end, function(i)
	local __new_lifted_lambda_1 = function(i)
		
		return i
	end
	return __new_lifted_lambda_1
end)
local fires = fi(1)
local fn = function(c, a)
	
	
	c.n = a
	return c.n
end
local swapG = function(a, f)
	
	return f(a.b, a.a)
end
local swapML = function(ml)
	
	return Tup(ml.b, ml.a)
end
fn({a = 1, n = {month = 2, weekday = 5, year = 1999}}, {month = 3, weekday = 5, year = 1999})
local btool = fn({a = 4, n = false, x = "Hello"}, true)
local mlres = swapML(Tup(st, Tup(1, st.pet)))
write("mlres is: ")
println(mlres)
local identity = function(a)
	
	return a
end
fst = newOpenFunction()
newOpenInstance(fst, function(s) return IsType(s, function(a) return IsNamedType({namedTypeSpec = {name = "Tup", args = {function(a) return AnyMatching({constraintSpec = {}})(a) end, function(a) return AnyMatching({constraintSpec = {}})(a) end}}})(a) end) end, function(s)
	return identity(s.a)
end)
local snd = function(s)
	
	return fst(swapML(s))
end
local tres = snd(s)
write("tres is: ")
println(tres)
local idresf = function(s)
	local __new_lifted_lambda_2
	
	
	local __new_lifted_lambda_2 = function(a, b)
		
		return Tup(a, b)
	end
	return identity(apply(identity, swapG(s, __new_lifted_lambda_2)))
end
local idres = idresf(s)
write("idres is: ")
println(idres)
local ftr = function(a, b)
	
	
	if not IsType(b, function(a) return IsPerson(a) end) then
		
		return add(add(b.species, " "), b.name)
	else
		
		return add(add(b.pet.species, " "), b.name)
	end
	return add(b.name, a)
end
local flr = function(x)
	
	if IsType(x, function(a) return IsPerson(a) end) then
		
		return {x = 1}
	else
		
		return ftr(x.species, x)
	end
end
if IsType(x, function(a) return IsInt(a) end) then
	
	b = lt(x, 10) and ftr("Hello ", st) or false
else

end
local basicPerson = function(name, age, male)
	
	return {age = age, male = male, name = name, parent = {}, pet = {color = "White", name = "Tom", species = "Cat"}}
end