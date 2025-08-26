// Please transleate this test in to node.js code

const loopCount = 1000000;
let val = 0;
let startTime = Date.now();
for (let i = 0; i < loopCount; i++) {
    val = i - 0.1 + val;
}
let endTime = Date.now();
let executionTime = endTime - startTime;
console.log(`Execution time: ${executionTime} milliseconds`);
console.log(`Val is ${val}`);

console.log("---");

eval(`
const loopCount = 1000000;
let val = 0.0;
let startTime = Date.now();
for (let i = 0; i < loopCount; i++) {
    val = i - 0.1 + val;
}
let endTime = Date.now();
let executionTime = endTime - startTime;
console.log(\`Execution time: \${executionTime} milliseconds\`);
console.log(\`Val is \${val}\`);
`);

console.log("---");

let loopCount2 = 1000000;
val = 0;
startTime = Date.now();
for (let i = 0; i < loopCount2; i++) {
    eval('val = i - 0.1 + val');
}
endTime = Date.now();
executionTime = endTime - startTime;
console.log(`Execution time: ${executionTime} milliseconds`);
console.log(`Val is ${val}`);

