# How to run:
# go build || exit 99
# rm -f /usr/local/bin/linescript4
# cp "$(pwd)/linescript4" /usr/local/bin/linescript4
# rm -f /usr/local/linescript4
# ln -s "$(pwd)" /usr/local/linescript4
# ./linescript4 linescript4_test.ls

 # say  "hi"
# exit

# "hi" ++ " world" upper  slice 1 4  as part
# assertEq "HI W" part
# exit

assertEq 300 300

var myList [10 20 30 40 50]
assertSame myList slice 1 -1, [10 20 30 40 50]
assertSame myList slice 3 -1, [30 40 50]
assertSame myList slice 2 -2, [20 30 40]
assertSame myList slice -3 -1, [30 40 50]
assertSame myList slice -3 -2, [30 40]
assertSame myList slice -200 -1, [10 20 30 40 50]
assertSame myList slice -200 -2, [10 20 30 40]
assertSame myList slice 1 200, [10 20 30 40 50]
assertSame myList slice 6 -1, []
assertSame myList slice 3 -300, []
assertSame myList slice 1 0, []

var a 3 + 4
assertEq a 7

var b 3 \
+ 4
assertEq b 7


assertSame [1] [1]
assertNotEq [1] [1]
assertSame [1] [1]
assertSame {a 100 b 200} {a 100 b 200}
assertNotSame {a 100 b 200} {a 100 b 200 c 300}

var myList [10 20 30 40 50]
var spliced myList splice 3 4 null
assertSame spliced [30 40]

someFuncWithSay "hi"
assertEq it 300

def someFuncWithSay
    say arguments
    300
end


getCurrentLine #wow
assertEq it "getCurrentLine #wow"

assertEq true {myKey 20} has myKey
assertEq false {myKey 20} has otherKey


assertEq toSource {
    a "yo"
    b "yo2"
}, string
    {
        a "yo"
        b "yo2"
    }
end


toSource {
    a "yo"
    b "yo2"
    c {
        d 1
    }
}
string
    {
        a "yo"
        b "yo2"
        c {
            d 1
        }
    }
end
assertEq it it "toSource map"

toSource [1 2 3]
string
    [
        1
        2
        3
    ]
end
assertEq it it "yow"

toSource [1 {b 2} 3]
string
    [
        1
        {
            b 2
        }
        3
    ]
end
assertEq it it "yow"


assertSame ["a" "b" "c"] parseFields "a    b  c"
assertSame ["a" "b" "c"] parseFields "  a    b  c"
assertSame ["a" "b" "c"] parseFields "  a    b  c   "



assertEq "yo" findBetween "@yo*" "@" "*"
assertEq "yo" findBetween "AAAyoBBB" .AAA .BBB
assertEq "yo" findBetween "?AAAyoBBB?" .AAA .BBB
assertEq "yo" findBetween "AyoA" .A .A

assertEq 15.0 "15.0" toFloat

assertEq [1] at 2, null
assertEq "a" at 2, ""
assertEq "a" slice 3 4, ""


let val 100
true and let val 101
assertEq val 101

false and let val 102
assertEq val 101



goDown Hi
assertEq 1 0 "should not get here"
label Hi


def setTimeout ms action
    go
        sleepMs ms
        action
    end
end


var messages []
var timeout2 setTimeout 20 func: messages push "100ms later"
sleepMs 30; messages push "slept 30"
def doIt myFunc
    messages push .doing
    myFunc
    messages push .done
end
doIt func
    messages push "ook"
end
doIt func: messages push "ook2"
assertSame messages [
    "100ms later"
    "slept 30"
    "doing"
    "ook"
    "done"
    "doing"
    "ook2"
    "done"
]

[1 2 3] each: update theSum + it
assertEq theSum 6


[1 2 3] each: myList2 push 1 + it
assertSame myList2 [2 3 4]

yo := 101
assertEq yo 101

yo2 = 102
assertEq yo2 102

# this no work
# yo2 = 103
# assertEq yo2 103


someObj99 to someProp .someVal
assertSame someObj99 {
    someProp .someVal
}



# 3 loop i
#     say "wow" i
#     func
#     
#     end
# end

var yo true and {
    hi "World"
}

assertSame yo {
    hi "World"
}

var yo false and [
]
assertEq yo false


var a [1 2 3 4]
assertSame (a slice 1 1) [1]
assertSame (a slice 1 0) []

def increr
    var x 0
    func
        let x x + 1
        x
    end
end
var myIncr increr
assertEq myIncr, 1
assertEq myIncr, 2

showTestOutput


# this fails
# false and say [
#     "yo"
# ]
