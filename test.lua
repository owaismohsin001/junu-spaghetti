require 'runtime'

local IsPet

local Pet
local IsMoo

local Moo
local IsPerson

local Person
local Date

local IsDate
local IsTup

local Tup
local IsNil

local Nil
local Array

local IsArray
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
local petPlusPet


IsPet = function(a) return IsStruct({structSpec = {color = function(a) return IsString(a) end, name = function(a) return IsString(a) end, species = function(a) return IsString(a) end}})(a) end
IsMoo = function(a) return IsStruct({structSpec = {age = function(a) return IsInt(a) end, male = function(a) return IsBool(a) end, name = function(a) return IsString(a) end, pet = function(a) return IsPet(a) end}})(a) end
IsPerson = function(a) return IsStruct({structSpec = {age = function(a) return IsInt(a) end, male = function(a) return IsBool(a) end, name = function(a) return IsString(a) end, parent = function(a) return Choice({function(a) return IsNil(a) end, function(a) return IsPerson(a) end})(a) end, pet = function(a) return IsPet(a) end}})(a) end
IsDate = function(a) return IsStruct({structSpec = {month = function(a) return IsInt(a) end, weekday = function(a) return IsInt(a) end, year = function(a) return IsInt(a) end}})(a) end
function Tup(x1, x2) return { _type = "Tup", _args = {x1, x2}, a = x1, b = x2} end
IsNil = function(a) return IsStruct({structSpec = {}})(a) end
function Array(x1) return { _type = "Array", _args = {x1}, _value = x1} end
println("\n\n\nProgram begins: \n")
s = Tup(1, true)
x = s.a
b = s.b
x = 4
i = 0
fl = function(a, b)
	local __new_lifted_lambda_1
	
	
	__new_lifted_lambda_1 = function(n)
		local __new_lifted_lambda_2
		
		
		__new_lifted_lambda_2 = function(h)
			local __new_lifted_lambda_3
			
			
			__new_lifted_lambda_3 = function()
				
				return h.name
			end
			return __new_lifted_lambda_3
		end
		return __new_lifted_lambda_2
	end
	return __new_lifted_lambda_1
end
go = function(a, b)
	local f
	
	local ans
	
	
	f = function(n)
		local zoo
		
		
		zoo = mul(n, 3)
		return n
	end
	ans = add(a, b)
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
apply = function(f, x)
	
	return f(x)
end
given = fl(1, true)(true)({color = "Black", name = "Hello's kitty", species = "Cat"})()
__new_lifted_lambda_0 = function(a)
	
	return eq(a, 1)
end
application = apply(__new_lifted_lambda_0, 1)
changeCatName = function(person, name)
	local f
	
	
	f = function()
		
		if lt(person.age, 5) then
			local catties
			
			
			
			
			catties = 1
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
modifyAge = function(person, age)
	
	
	person.age = lt(age, 0) and 0 or age
	return age
end
st = {age = 10, male = true, name = "Ameer", parent = {}, pet = {color = "White", name = "Tom", species = "Cat"}}
st.parent = duplicate(st)
nm1 = changeCatName(st, "Molly")
ag1 = modifyAge(st, add(st.age, 1))
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
sn = setName("Junu", "Collatz", {pet = st})
write("sn is: ")
println(sn)
fi = newOpenFunction()
newOpenInstance(fi, function(i) return IsType(i, function(a) return IsInt(a) end) end, function(i)
	__new_lifted_lambda_1 = function(i)
		
		return i
	end
	return __new_lifted_lambda_1
end)
fires = fi(1)
fn = function(c, a)
	
	
	c.n = a
	return c.n
end
swapG = function(a, f)
	
	return f(a.b, a.a)
end
swapML = function(ml)
	
	return Tup(ml.b, ml.a)
end
fn({a = 1, n = {month = 2, weekday = 5, year = 1999}}, {month = 3, weekday = 5, year = 1999})
btool = fn({a = 4, n = false, x = "Hello"}, true)
mlres = swapML(Tup(st, Tup(1, st.pet)))
write("mlres is: ")
println(mlres)
identity = function(a)
	
	return a
end
fst = newOpenFunction()
newOpenInstance(fst, function(s) return IsType(s, function(a) return IsNamedType({namedTypeSpec = {name = "Tup", args = {function(a) return AnyMatching({constraintSpec = {}})(a) end, function(a) return AnyMatching({constraintSpec = {}})(a) end}}})(a) end) end, function(s)
	return identity(s.a)
end)
newOpenInstance(add, function(a, b) return IsType(a, function(a) return IsPet(a) end) and IsType(b, function(a) return IsPet(a) end) end, function(a, b)
	return {color = b.color, name = add(add(a.name, " "), b.name), species = eq(a.species, b.species) and a.species or add(add(a.species, " with "), b.species)}
end)
snd = function(s)
	
	return fst(swapML(s))
end
tres = snd(s)
write("tres is: ")
println(tres)
idresf = function(s)
	local __new_lifted_lambda_2
	
	
	__new_lifted_lambda_2 = function(a, b)
		
		return Tup(a, b)
	end
	return identity(apply(identity, swapG(s, __new_lifted_lambda_2)))
end
idres = idresf(s)
write("idres is: ")
println(idres)
ftr = function(a, b)
	
	
	if not IsType(b, function(a) return IsPerson(a) end) then
		
		return add(add(b.species, " "), b.name)
	else
		
		return add(add(b.pet.species, " "), b.name)
	end
	return add(b.name, a)
end
flr = function(x)
	
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
basicPerson = function(name, age, male)
	
	return {age = age, male = male, name = name, parent = {}, pet = {color = "White", name = "Tom", species = "Cat"}}
end
petPlusPet = add(st.pet, {color = "Black", name = "Tom", species = "Dog"})
write("petPlusPet is: ")
println(petPlusPet)