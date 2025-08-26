# How to run:
# go build || exit 99
# rm -f /usr/local/bin/linescript4
# cp "$(pwd)/linescript4" /usr/local/bin/linescript4
# rm -f /usr/local/linescript4
# ln -s "$(pwd)" /usr/local/linescript4
# ./linescript4 linescript4_test.ls

# TODO bug where a function starts at first line of file

# TODO: lazily load stdlib, part of hoisting
var assertionCount 0
var failureCount 0

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
        exit
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
        exit
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
            if not v sameAs got at %i
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

def showTestOutput
    say %%
        %assertionCount assertions made
        %failureCount failures
    end
    if failureCount > 0
        say .FAIL
    else
        say .PASS
    end
end

def parseFields str
    var chars []
    var prev ""
    
    str each c
        var trimmed c trim
        if trimmed is "", and prev is ""
        else
            chars push c
        end
        let prev trimmed
    end
    chars
end

def parseFields str
    var chars []
    var prev ""
    
    str each c
        var trimmed c trim
        if trimmed is "", and prev is ""
        else
            chars push c
        end
        let prev trimmed
    end
    chars join "", trim, split " "
end

def findBetween s after before
    var startI s indexOf after
    if startI is 0
        return ""
    end
    
    var afterPart s slice startI (+ len after) -1
    var endI afterPart indexOf before
    if endI is 0
        return ""
    end
    
    afterPart slice 1 endI - 1
end