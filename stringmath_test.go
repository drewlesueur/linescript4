package main

import (
   "testing"
   "time"
   "fmt"
)

func TestAdd(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		// Basic additions
		{"1.3", "2.57", "3.87"},
		{"2.57", "1.3", "3.87"},
		{"123", "456", "579"},
		{"0", "0", "0"},
		// Mixed signs
		{"-1.3", "2.57", "1.27"},
		{"1.3", "-2.57", "-1.27"},
		{"-1.3", "-2.57", "-3.87"},
		// Fractional arithmetic
		{"0.1", "0.2", "0.3"},
		{"99.99", "0.01", "100"},
		{"12.345", "0.655", "13"}, // trailing zeros removed
		{"0.99", "0.02", "1.01"},
		// With leading zeros in integer parts
		{"001.3", "02.57", "3.87"},
		{"001.3", "02.5700000", "3.87"},
		{"000", "000001", "1"},
		{"0.9999999999999999999999999999999999999999999999", "0.0000000000000000000000000000000000000000000001", "1"},
	}

	for _, tc := range tests {
		result := Add(tc.a, tc.b)
		if result != tc.expected {
			t.Errorf("Add(%q, %q) = %q; expected %q", tc.a, tc.b, result, tc.expected)
		}
	}
}
func TestMod(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		// Basic additions
		{"10", "6", "4"},
	}

	for _, tc := range tests {
		result := Mod(tc.a, tc.b)
		if result != tc.expected {
			t.Errorf("Mod(%q, %q) = %q; expected %q", tc.a, tc.b, result, tc.expected)
		}
	}
}

func TestSubtract(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		// Basic subtractions
		{"2.57", "1.3", "1.27"},
		{"1.3", "2.57", "-1.27"},
		{"456", "123", "333"},
		{"0", "0", "0"},
		// Mixed signs
		{"-1.3", "2.57", "-3.87"},
		{"2.57", "-1.3", "3.87"},
		{"-1.3", "-2.57", "1.27"},
		// Borrowing across the decimal point
		{"1.00", "0.01", "0.99"},
		{"100", "99.99", "0.01"},
		{"100", "99.990000000", "0.01"},
		// Borrowing across integer part digits
		{"1000", "1", "999"},
	}

	for _, tc := range tests {
		result := Subtract(tc.a, tc.b)
		if result != tc.expected {
			t.Errorf("Subtract(%q, %q) = %q; expected %q", tc.a, tc.b, result, tc.expected)
		}
	}
}

func TestParse(t *testing.T) {
	tests := []struct {
		input          string
		expectedSign   string
		expectedInt    string
		expectedFrac   string
	}{
		{input: "123.456", expectedSign: "+", expectedInt: "123", expectedFrac: "456"},
		{input: "-123.456", expectedSign: "-", expectedInt: "123", expectedFrac: "456"},
		{input: "123", expectedSign: "+", expectedInt: "123", expectedFrac: ""},
		{input: "-123", expectedSign: "-", expectedInt: "123", expectedFrac: ""},
		{input: "+123.456", expectedSign: "+", expectedInt: "123", expectedFrac: "456"},
		{input: "-0.001", expectedSign: "-", expectedInt: "0", expectedFrac: "001"},
		{input: "0", expectedSign: "+", expectedInt: "0", expectedFrac: ""},
		{input: "0.0", expectedSign: "+", expectedInt: "0", expectedFrac: "0"},
	}

	for _, tc := range tests {
		sign, intPart, fracPart := parse(tc.input)
		if sign != tc.expectedSign || intPart != tc.expectedInt || fracPart != tc.expectedFrac {
			t.Errorf("parse(%q) = (%q, %q, %q); expected (%q, %q, %q)", 
				tc.input, sign, intPart, fracPart, 
				tc.expectedSign, tc.expectedInt, tc.expectedFrac)
		}
	}
}


func TestMultiply(t *testing.T) {
	tests := []struct {
		a, b, expected string
	}{
		// Basic multiplications
		{"2", "3", "6"},
		{"0", "123.456", "0"},
		{"123", "0", "0"},
		{"4", "0.25", "1"},
		{"-2", "3", "-6"},
		{"-123.456", "1", "-123.456"},
		// Mixed signs
		{"-2.5", "-4", "10"}, // both negative
		{"2.5", "-4", "-10"},  // one negative
		// Testing decimal multiplication
		{"1.5", "2.5", "3.75"},
		{"0.1", "0.2", "0.02"},
		// Large numbers
		{"123456789", "987654321", "121932631112635269"},
	}
	
	for _, tc := range tests {
		result := Multiply(tc.a, tc.b)
		if result != tc.expected {
			t.Errorf("Multiply(%q, %q) = %q; expected %q", tc.a, tc.b, result, tc.expected)
		}
	}
}



func TestDivide(t *testing.T) {
	tests := []struct {
		a, b, expected string
		precision int
	}{
		// Basic divisions
		{"6", "3", "2", 10},
		{"100", "10", "10", 10},
		{"123.456", "1", "123.456", 10},
		{"1", "3", "0.3333333333", 10}, // Repeating decimal
		{"0", "123.456", "0", 10},
		// Division by zero
		{"123.456", "0", "NaN", 10},
		// Mixed signs
		{"6", "-3", "-2", 10},
		{"-6", "3", "-2", 10},
		{"-6", "-3", "2", 10},
		// Decimal divisions
		{"1.5", "0.3", "5", 10},
		{"0.1", "0.2", "0.5", 10},
		// Large numbers
		{"123456789", "987654321", "0.1249999989", 10},
	}

	for _, tc := range tests {
		result := Divide(tc.a, tc.b, tc.precision)
		if result != tc.expected {
			t.Errorf("Divide(%q, %q, %d) = %q; expected %q", tc.a, tc.b, tc.precision, result, tc.expected)
		}
	}
}



func TestPowPositiveExponent(t *testing.T) {
	tests := []struct {
		base      string
		exp       string
		precision int
		expected  string
	}{
		// Simple integral powers.
		{"2", "3", 10, "8"},
		{"3", "4", 10, "81"},
		{"2", "10", 10, "1024"},
		// Decimal base.
		{"2.5", "2", 10, "6.25"},
		{"1.2", "3", 10, "1.728"},
		// {"25", ".5", 1, "1.728"}, // slow!
		// Larger exponent.
		{"1.1", "5", 10, "1.61051"},
	}

	for _, tt := range tests {
		result := Pow(tt.base, tt.exp, tt.precision)
		if result != tt.expected {
			t.Errorf("Pow(%s, %s) = %s, expected %s", tt.base, tt.exp, result, tt.expected)
		}
	}
}

func TestPowNegativeExponent(t *testing.T) {
	tests := []struct {
		base      string
		exp       string
		precision int
		expected  string
	}{
		// Negative exponent cases; using a precision of 10 digits.
		{"2", "-3", 10, "0.125"},
		{"5", "-2", 10, "0.04"},
		{"2.5", "-1", 10, "0.4"},
	}

	for _, tt := range tests {
		result := Pow(tt.base, tt.exp, tt.precision)
		if result != tt.expected {
			t.Errorf("Pow(%s, %s) = %s, expected %s", tt.base, tt.exp, result, tt.expected)
		}
	}
}

func TestPowZeroExponent(t *testing.T) {
	// Any number raised to the 0 power should equal 1.
	result := Pow("123.456", "0", 10)
	if result != "1" {
		t.Errorf("Pow(123.456, 0) = %s, expected 1", result)
	}
}

func TestPowOneExponent(t *testing.T) {
	result := Pow("-7.89", "1", 10)
	if result != "-7.89" {
		t.Errorf("Pow(-7.89, 1) = %s, expected -7.89", result)
	}
}

func TestPowEdgeCaseZeroBaseNegativeExp(t *testing.T) {
	// 0 raised to a negative exponent is undefined.
	// Our Divide function will return "NaN" when dividing by zero.
	result := Pow("0", "-3", 10)
	if result != "NaN" {
		t.Errorf("Pow(0, -3) = %s, expected NaN", result)
	}
}

func TestPowLargeExponent(t *testing.T) {
	// Test with a moderately large exponent.
	result := Pow("1.01", "20", 10)
	// Expected result approximated manually: 1.01^20 ≈ 1.2201900399...
	expected := "1.22019"
	// We compare only the beginning digits.
	if result[:7] != expected {
		t.Errorf("Pow(1.01, 20) = %s, expected prefix %s", result, expected)
	}
}

type Foo struct {
    Int int
}

type FastObject struct {
    Slice []any
    KeyPositions map[string]int
}

func NewFastObject() *FastObject {
    return &FastObject{KeyPositions: map[string]int{}}
}

func (f *FastObject) Set(key string, value any) int {
    if pos, exists := f.KeyPositions[key]; exists {
        f.Slice[pos] = value
        return pos
    } else {
        f.KeyPositions[key] = len(f.Slice)
        f.Slice = append(f.Slice, value)
        return pos
    }
}
func (f *FastObject) Get(key string) (any) {
    pos, exists := f.KeyPositions[key]
    if !exists {
        return nil
    }
    return f.Slice[pos]
}
    
// make a similar type as FastObject called GenericFastObject
// but instead of any, use a type parameter (generics)
// to allow it to be an int, string, float64, or another GenericFastObject



func xTestPerf2(t *testing.T) {
	total := "0"
	totalFloat := 0.0
	totalInt := 0

	loops := 10_000_000
	startTime := time.Now()
	// for i := 0; i < loops; i++ {
	// 	total = Add(total, "1")
	// }
	duration := time.Since(startTime)
	fmt.Printf("Duration for %d Add (%v): %v\n", loops, total, duration)
	
	total = "0"
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		total = FastAdd(total, "1")
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d FastAdd (%v): %v\n", loops, total, duration)
	
	

	startTime = time.Now()
	for i := 0; i < loops; i++ {
		// total += 9999999999
		totalFloat += 1
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d + (%v): %v\n", loops, totalFloat, duration)


	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt += 1
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d + (%v): %v\n", loops, totalInt, duration)

    totalInt = 0
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt = AddAny(totalInt, get1()).(int)
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d AddAny (%v): %v\n", loops, totalInt, duration)
	
	
    totalInt = 0
    foo := Foo{1}
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt += foo.Int
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d Struct (%v): %v\n", loops, totalInt, duration)

    totalInt = 0
    fooP := &Foo{1}
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt += fooP.Int
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d StructP (%v): %v\n", loops, totalInt, duration)
    
    
    totalInt = 0
    fooMap := map[string]any{"Int": 1}
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt += fooMap["Int"].(int)
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d Map (%v): %v\n", loops, totalInt, duration)

    totalInt = 0
    fooFast := NewFastObject()
    fooFast.Set("Int", 1) 
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt += fooFast.Get("Int").(int)
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d FO (%v): %v\n", loops, totalInt, duration)

    totalInt = 0
    fooFast = NewFastObject()
    index := fooFast.Set("Int", 1) 
	startTime = time.Now()
	for i := 0; i < loops; i++ {
		totalInt += fooFast.Slice[index].(int)
	}
	duration = time.Since(startTime)
	fmt.Printf("Duration for %d FOC (%v): %v\n", loops, totalInt, duration)
}

func get1() any {
    return 1
}


func AddAny(a any, b any) any {
    return a.(int) + b.(int)
}

func TestLessThan(t *testing.T) {
	tests := []struct {
		a, b     string
		expected bool
	}{
		{"1", "2", true},
		{"2", "1", false},
		{"-2", "-1", true},
		{"-1", "0", true},
		{"0", "0", false},
		{"001", "1", false},
		{"1.0", "1", false},
		{"-0", "0", false},
		{"1.000", "1.001", true},
		{"24.5555", "8", false},
	}
	for _, tc := range tests {
		if LessThan(tc.a, tc.b) != tc.expected {
			t.Errorf("LessThan(%q, %q) = %v; expected %v", tc.a, tc.b, LessThan(tc.a, tc.b), tc.expected)
		}
	}
}

func TestGreaterThan(t *testing.T) {
	tests := []struct {
		a, b     string
		expected bool
	}{
		{"1", "2", false},
		{"2", "1", true},
		{"-2", "-1", false},
		{"-1", "0", false},
		{"0", "0", false},
		{"001", "1", false},
		{"1.0", "1", false},
		{"-0", "0", false},
		{"1.001", "1.000", true},
	}
	for _, tc := range tests {
		if GreaterThan(tc.a, tc.b) != tc.expected {
			t.Errorf("GreaterThan(%q, %q) = %v; expected %v", tc.a, tc.b, GreaterThan(tc.a, tc.b), tc.expected)
		}
	}
}

func TestLessThanOrEqualTo(t *testing.T) {
	tests := []struct {
		a, b     string
		expected bool
	}{
		{"1", "2", true},
		{"2", "1", false},
		{"-2", "-1", true},
		{"-1", "0", true},
		{"0", "0", true},
		{"001", "1", true},
		{"1.0", "1", true},
		{"-0", "0", true},
		{"1.001", "1.000", false},
	}
	for _, tc := range tests {
		if LessThanOrEqualTo(tc.a, tc.b) != tc.expected {
			t.Errorf("LessThanOrEqualTo(%q, %q) = %v; expected %v", tc.a, tc.b, LessThanOrEqualTo(tc.a, tc.b), tc.expected)
		}
	}
}

func TestGreaterThanOrEqualTo(t *testing.T) {
	tests := []struct {
		a, b     string
		expected bool
	}{
		{"1", "2", false},
		{"2", "1", true},
		{"-2", "-1", false},
		{"-1", "0", false},
		{"0", "0", true},
		{"001", "1", true},
		{"1.0", "1", true},
		{"-0", "0", true},
		{"1.001", "1.000", true},
	}
	for _, tc := range tests {
		if GreaterThanOrEqualTo(tc.a, tc.b) != tc.expected {
			t.Errorf("GreaterThanOrEqualTo(%q, %q) = %v; expected %v", tc.a, tc.b, GreaterThanOrEqualTo(tc.a, tc.b), tc.expected)
		}
	}
}

func TestEqual(t *testing.T) {
	tests := []struct {
		a, b     string
		expected bool
	}{
		{"1", "1", true},
		{"1", "2", false},
		{"-1", "-1", true},
		{"-1", "1", false},
		{"0", "0", true},
		{"001", "1", true},
		{"1.0", "1", true},
		{"1.000", "1.0", true},
		{"-0", "0", true},
		{"0", "", true},
	}
	for _, tc := range tests {
		if Equal(tc.a, tc.b) != tc.expected {
			t.Errorf("Equal(%q, %q) = %v; expected %v", tc.a, tc.b, Equal(tc.a, tc.b), tc.expected)
		}
	}
}
