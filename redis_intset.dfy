method intsetMoveTail(is: array<int>, from: nat, to: nat) returns (is_ret: array<int>)
	modifies is
{
	if (from < to) {
		var index := is.Length-1;
		while (index >= from) {
			is[index] := is[index-1];
			index := index - 1;
		}
	} else if (from > to) {
		var index := to;
		while (index < is.Length) {
			is[index] := is[index+1];
			index := index + 1;
		}
	}
	is_ret := is;
	return;
}
	
method intsetAdd(is: array<int>, value: int) returns (success: bool, is_ret: array<int>)
	ensures success <==> is_ret.Length == is.Length + 1
	modifies is
{
	success := true;
	var pos: nat, found: bool := intsetSearch(is, value);
	
	if (found) {
		success := false;
		is_ret := is;
		return;
	}

	is_ret := intsetResize(is, is.Length+1);
	if (pos < is_ret.Length) {
		is_ret := intsetMoveTail(is_ret, pos, pos+1);
	}
	
	is_ret := intsetSet(is_ret, pos, value);
	return;
}
	

/* Search for the position of "value". Return 1 when the value was found and
 * sets "pos" to the position of the value within the intset. Return 0 when
 * the value is not present in the intset and sets "pos" to the position
 * where "value" can be inserted. */
method intsetSearch(is: array<int>, value: int) returns (pos: nat, found: bool)
  ensures is.Length > 0 ==> pos <= is.Length
	ensures !found ==> forall k :: 0 <= k < is.Length ==> is[k] != value
	ensures is.Length > 0 && value > is[is.Length-1] ==> pos == is.Length
	ensures is.Length == 0 ==> !found
	ensures found ==> is.Length >= 1
{
	var min: int, max: int, mid: int := 0, is.Length - 1, -1;
	var cur: int := -1;
	found := false;
  pos := 0;
	if is.Length == 0 {
		pos := 0;
		found := false;
		return;
	} else {
		/* Check for the case where we know we cannot find the value,
       but do know the insert position. */
		var temp1 := p_intsetGet(is, max);
		var temp2 := p_intsetGet(is, 0);
		if (value > temp1) {
			pos := is.Length;
			found := false;
			return;
		} else if (value < temp2) {
			pos := 0;
			found := false;
			return;
		}
	}

	while max >= min {
		mid := (min + max) / 2;
		cur := p_intsetGet(is, mid);
		if (value > cur) {
			min := mid + 1;
		} else if (value < cur) {
			max := mid - 1;
		} else {
			break;
		}
	}

	if (value == cur) {
		pos := mid;
		found := true;
		return;
	} else {
		pos := min;
		found := false;
		return;
	}
}

// Possible flaw: this method assumes that the caller will perform a range check.
// No actual checking is done in this private method in the source code.
method p_intsetGet(is: array<int>, pos: int) returns (value: int)
	requires 0 <= pos && pos < is.Length
{
	value := is[pos];
	return;
}

method intsetGet(is: array<int>, pos: nat) returns (value: int, inRange: bool)
	// In the redis code, pos is a uint32_t, ensuring that the value can not be negative.
{
	if (pos < is.Length) {
		value := p_intsetGet(is, pos);
		inRange := true;
		return;
	}
	inRange := false;
	return;
}

method intsetSet(is: array<int>, pos: nat, value: int) returns (is_ret: array<int>)
	modifies is
{
	is[pos] := value;
	is_ret := is;
	return;
}

method intsetRemove(is: array<int>, value: nat) returns (success: bool, is_ret: array<int>)
	requires is.Length >= 1
	modifies is
{
  success := false;
	var pos: nat, found: bool := intsetSearch(is, value);	
	if (found) {
		success := true;
		if (pos < (is.Length - 1)) {
			is_ret := intsetMoveTail(is, pos+1, pos);
			is_ret := intsetResize(is_ret, is_ret.Length - 1);
		}
	}
	return;
}

method intsetResize(is: array<int>, len: nat) returns (is_ret: array<int>)
	ensures is_ret.Length == len
	ensures len < is.Length ==> forall k :: 0 <= k < is_ret.Length ==> is[k] == is_ret[k]
	ensures len > is.Length ==> forall k :: 0 <= k < is.Length ==> is[k] == is_ret[k]
{
	is_ret := new int[len];
	var index := 0;
	while index < len 
	{
		if (index >= is.Length)
		{
			is_ret[index] := 0;
		} else {
			is_ret[index] := is[index];
		}
		index := index + 1;
	}
	return;
}

method intsetNew() returns (is: array<int>)
	ensures is != null
	ensures is.Length == 0
{
	is := new int[0];
	print(is.Length);
	return;
}

// Return the length of the intset
method intsetLen(is: array<int>) returns (length: nat)
// Length should not be negative
 ensures length >= 0
 ensures length == is.Length
{
    length := is.Length;
    return;
}

// Return true if the value is in the intset; false if not.
method intsetFind(is: array<int>, value: nat) returns (found: bool)
	// If method returns false, value should not be found in the array.
	ensures !found ==> forall k :: 0 <= k < is.Length ==> is[k] != value
	// If the method return, value should be in the array.
	ensures found ==> exists k :: 0 <= k < is.Length && is[k] == value
{
    var pos;
    pos, found := intsetSearch(is, value);
    return;
}
