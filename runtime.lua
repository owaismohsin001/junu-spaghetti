function IsString(a) return type(a) == "string" end
function IsInt(a) return type(a) == "number" end
function IsBool(a) return type(a) == "boolean" end

function Either(f1, f2)
    return function(a)
        if f1(a) then return true end
        if f2(a) then return true end
        return false
    end
end

function Choice(fs) return
    function(a)
        for _, f in ipairs(fs) do
            if f(a) then return true end
        end
        return false
    end
end

function tablelength(T)
    local count = 0
    for _ in pairs(T) do count = count + 1 end
    return count
end

function IsStruct(spec, struct)
    if tablelength(spec) ~= tablelength(struct) then return false end
    for k, v in pairs(struct) do
        if spec[k] == nil then return false end
        if not spec[k](v) then return false end
    end
    return true
end

function IsType(val, spec)
    if spec == "Int" then return IsInt(val) end
    if spec == "Bool" then return IsBool(val) end 
    if spec == "String" then return IsString(val) end
    if type(spec) == "function" then return spec(val) end
    if type(spec) == "table" then
        if type(val) == "function" and spec.functionSpec ~= nil then return true end
        if type(val) == "table" and spec.structSpec ~= nil then return IsStruct(spec.structSpec, val) end
    end
    return false
end

eq = function(a, b) return a==b end
neq = function(a, b) return a~=b end
gt = function(a, b) return a>b end
gte = function(a, b) return a>=b end
lt = function(a, b) return a<b end
lte = function(a, b) return a<=b end
add = function(a, b) return a+b end
sub = function(a, b) return a-b end
mul = function(a, b) return a*b end
div = function(a, b) return a/b end
mod = function(a, b) return math.mod(a, b) end
anded = function(a, b) return a and b end
ored = function(a, b) return a or b end

-- print(IsType({a = "nu", b = 1}, {structSpec = {a = IsString, b = Choice({IsBool, IsInt})}}))