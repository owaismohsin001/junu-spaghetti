function Array(x1) return { _type = "Array", _args = {x1}, a = x1} end

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

function Choice(fs) 
    return function(a)
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

function IsStruct(spec)
    local spec = spec.structSpec
    return function(struct)
        if type(struct) ~= "table" then return false end
        if spec == nil then return false end
        if tablelength(spec) ~= tablelength(struct) then return false end
        for k, v in pairs(struct) do
            if spec[k] == nil then return false end
            if not spec[k](v) then return false end
        end
        return true
    end
end

function AnyMatching(spec)
    local spec = spec.constraintSpec
    return function(struct)
        if spec == nil then return false end
        if next(spec) == nil then return true end
        if type(struct) ~= "table" then return false end
        for k, f in pairs(spec) do
            if struct[k] == nil then return false end
            if not f(struct[k]) then return false end
        end
        return true
    end
end

function IsNamedType(spec)
    local spec = spec.namedTypeSpec
    return function(typ)
        if spec == nil then return false end
        if type(typ) ~= "table" then return false end
        if typ._type ~= spec.name then return false end
        if tablelength(spec.args) ~= tablelength(typ._args) then return false end
        for k, v in ipairs(typ._args) do
            if spec.args[k] == nil then return false end
            if not spec.args[k](v) then return false end
        end
        return true
    end
end

function getArgs(fun)
    local args = {}
    local hook = debug.gethook()
    
    local argHook = function( ... )
        local info = debug.getinfo(3)
        if 'pcall' ~= info.name then return end
    
        for i = 1, math.huge do
            local name, value = debug.getlocal(2, i)
            if '(*temporary)' == name or name == nil then
                debug.sethook(hook)
                error('')
                return
            end
            table.insert(args,name)
        end
    end
    
    debug.sethook(argHook, "c")
    pcall(fun)
    
    return args
end

function IsFunction(argNum)
    return function(f)
        if type(f) ~= "function" then return false end
        return tablelength(getArgs(f)) == argNum
    end
end

function IsType(val, spec)
    if spec == "Int" then return IsInt(val) end
    if spec == "Bool" then return IsBool(val) end 
    if spec == "String" then return IsString(val) end
    if type(spec) == "function" then return spec(val) end
    if type(spec) == "table" then
        if type(val) == "function" and spec.functionSpec ~= nil then return true end
        if type(val) == "table" and spec.constraintSpec ~= nil then return AnyMatching(spec)(val) end
        if type(val) == "table" and spec.structSpec ~= nil then return IsStruct(spec)(val) end
        if type(val) == "table" and val ~= nil and val._type ~= nil and spec.namedTypeSpec ~= nil then return IsNamedType(spec)(val) end
    end
    return false
end

eq = function(a, b) return a==b end
neq = function(a, b) return a~=b end
gt = function(a, b) return a>b end
gte = function(a, b) return a>=b end
lt = function(a, b) return a<b end
lte = function(a, b) return a<=b end
add = function(a, b) return type(a) == "string" and a .. b or a+b end
sub = function(a, b) return a-b end
mul = function(a, b) return a*b end
div = function(a, b) return a/b end
mod = function(a, b) return math.mod(a, b) end
anded = function(a, b) return a and b end
ored = function(a, b) return a or b end

getWrappedArray = function(a)
    local axx = a.a
    local ax
    if type(axx) == "table" and axx._wrapped then 
        ax = axx._wrapped
    else
        ax = {axx}
    end
    return ax
end

concat = function(a, b)
    local ax, bx = getWrappedArray(a), getWrappedArray(b)
    local new_table = duplicate(ax)
    for _, v in ipairs(bx) do 
        table.insert(new_table, v)
    end
    return Array({_wrapped = new_table})
end

write = function(a)
    if type(a) == "table" and a._type and a._type == "Array" then
        io.write("[")
        local ax = getWrappedArray(a)
        for _, v in ipairs(ax) do
            write(v)
            io.write(", ")
        end
        io.write("]")
        return
    end
    if type(a) == "table" then
        if a._type ~= nil then 
            io.write(a._type)
            io.write("(")
            for _, v in pairs(a._args) do
                write(v)
                io.write(", ")
            end
            io.write(")")
            return
        end
        io.write("{")
        for k, v in pairs(a) do
            io.write(k)
            io.write(": ")
            write(v)
            io.write(", ")
        end
        io.write("}")
        return
    end
    io.write(tostring(a))
end

function duplicate(obj, seen)
    if type(obj) ~= 'table' then return obj end
    if seen and seen[obj] then return seen[obj] end
    local s = seen or {}
    local res = setmetatable({}, getmetatable(obj))
    s[obj] = res
    for k, v in pairs(obj) do res[duplicate(k, s)] = duplicate(v, s) end
    return res
end

function newOpenFunction() 
    local t = {}
    function f(t, ...)
        for _, pair in pairs(t) do
            pred, fn = unpack(pair)
            if pred(...) then return fn(...) end
        end
        print("oidoid")
        return nil
    end
    setmetatable(t, {__call = f})
    return t
end
function newOpenInstance(fTable, pred, body)
    table.insert(fTable, {pred, body})
end

println = function(a)
    write(a)
    io.write("\n")
    return a
end

-- print(IsType({a = "A", b = 3}, {constraintSpec = {a = IsString}}))
-- print(IsFunction(3)(function(a, b, c) return 0 end))
-- print(IsType({_type = "Tup", a = "A", b = 3, _args = {"A", 3}}, {namedTypeSpec = {name = "Tup", args = {IsString, Choice({IsInt, IsBool})}}}))