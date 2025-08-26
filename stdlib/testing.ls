def getCurrentLine
    getLineForState __state at CallingParent
end

def getLineForState theState
    var code theState at Code
    var endI theState at I
    
    var i endI
    forever
        update i - 1
        if i <= 0
            return code slice i endI
        end
        if code at %i, is newline
            return code slice i + 1, endI - 1
        end
    end
end


def getCallingLine
    var theState __state at CallingParent, at CallingParent, at CallingParent
    getLineForState theState
end


def assertEq
    update assertionCount + 1
    var [want got message] arguments
    if want isnt got
        update failureCount + 1
        say %%
            want   : %want
            got    : %got
            message: %message
            line: (%getCallingLine)
        end
    end
end
def assertNotEq
    update assertionCount + 1
    var [want got message] arguments
    if want is got
        update failureCount + 1
        say %%
            not want   : %want
            got        : %got
            message    : %message
            line: (%getCallingLine)
        end
    end
end
def assertSame
    update assertionCount + 1
    var [want got message] arguments
    
    if not want sameAs got
        update failureCount + 1
        say %%
            want   : %want
            got    : %got
            message: %message
            line: (%getCallingLine)
        end
        exit
    end
end
def assertNotSame
    update assertionCount + 1
    var [want got message] arguments
    if want sameAs got
        update failureCount + 1
        say %%
            not want   : %want
            got        : %got
            message    : %message
            line       : (%getCallingLine)
        end
        exit
    end
end

def sameAs want got
    var wantType getType want
    var gotType getType got
    if wantType isnt gotType
        return false
    end
    
    switch wantType
    case .record
        if want len, isnt got len
            return false
        end
        want each k v
            if not v sameAs got at %k
                return false
            end
        end
    case .list
        if want len, isnt got len
            return false
        end
        want each i v
            return v sameAs got at %i
                return false
            end
        end
    default
        if want isnt got
            return false
        end
    end
    return true
end