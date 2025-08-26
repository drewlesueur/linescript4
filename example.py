import time

loop_count = 1000000
val = 0
start_time = time.time()
for i in range(loop_count):
    # val = i - 0.1 + val
    val = i - 0.1 + val     #+ 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2
    # val = i - 1
end_time = time.time()
execution_time = (end_time - start_time) * 1000
print(f"Execution time: {execution_time} milliseconds")
print(f"Val is {val}")

print("---")
exit()

def test1(x):
    return x


loop_count = 1000000
val = 0
start_time = time.time()
for i in range(loop_count):
    # val = i - 0.1 + val
    val = i - test1(0.1) + val     #+ 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2 + 2 - 2
    # val = i - 1
end_time = time.time()
execution_time = (end_time - start_time) * 1000
print(f"Execution time: {execution_time} milliseconds")
print(f"Val is {val}")

print("---")
exit()

# const loopCount = 1000000;
# let val = 0;
# const startTime = Date.now();
# for (let i = 0; i < loopCount; i++) {
#   val = i - 0.1 + val;
# }
# const endTime = Date.now();
# const executionTime = endTime - startTime;
# log2(`Execution time: ${executionTime} milliseconds`);
# log2(`Val is ${val}`);


exec('''
loop_count = 1000000
val = 0.0
start_time = time.time()
for i in range(loop_count):
    val = i - 0.1 + val
end_time = time.time()
execution_time = (end_time - start_time) * 1000
print(f"Execution time: {execution_time} milliseconds")
print(f"Val is {val}")
''')

print("---")

loop_count = 1000000
val = 0
start_time = time.time()
for i in range(loop_count):
    exec('val = i - 0.1 + val')
end_time = time.time()
execution_time = (end_time - start_time) * 1000
print(f"Execution time: {execution_time} milliseconds")
print(f"Val is {val}")





