// Here is one of the functions that we are converting to Boogie:
/*
/* Insert an integer in the intset */
intset *intsetAdd(intset *is, int64_t value, uint8_t *success) {
    uint8_t valenc = _intsetValueEncoding(value);
    uint32_t pos;
    if (success) *success = 1;

    /* Upgrade encoding if necessary. If we need to upgrade, we know that
     * this value should be either appended (if > 0) or prepended (if < 0),
     * because it lies outside the range of existing values. */
    if (valenc > intrev32ifbe(is->encoding)) {
        /* This always succeeds, so we don't need to curry *success. */
        return intsetUpgradeAndAdd(is,value);
    } else {
        /* Abort if the value is already present in the set.
         * This call will populate "pos" with the right position to insert
         * the value when it cannot be found. */
        if (intsetSearch(is,value,&pos)) {
            if (success) *success = 0;
            return is;
        }

        is = intsetResize(is,intrev32ifbe(is->length)+1);
        if (pos < intrev32ifbe(is->length)) intsetMoveTail(is,pos,pos+1);
    }

    _intsetSet(is,pos,value);
    is->length = intrev32ifbe(intrev32ifbe(is->length)+1);
    return is;
}

/* Search for the position of "value". Return 1 when the value was found and
 * sets "pos" to the position of the value within the intset. Return 0 when
 * the value is not present in the intset and sets "pos" to the position
 * where "value" can be inserted. */
static uint8_t intsetSearch(intset *is, int64_t value, uint32_t *pos) {
    int min = 0, max = intrev32ifbe(is->length)-1, mid = -1;
    int64_t cur = -1;

    /* The value can never be found when the set is empty */
    if (intrev32ifbe(is->length) == 0) {
        if (pos) *pos = 0;
        return 0;
    } else {
        /* Check for the case where we know we cannot find the value,
         * but do know the insert position. */
        if (value > _intsetGet(is,max)) {
            if (pos) *pos = intrev32ifbe(is->length);
            return 0;
        } else if (value < _intsetGet(is,0)) {
            if (pos) *pos = 0;
            return 0;
        }
    }

    while(max >= min) {
        mid = ((unsigned int)min + (unsigned int)max) >> 1;
        cur = _intsetGet(is,mid);
        if (value > cur) {
            min = mid+1;
        } else if (value < cur) {
            max = mid-1;
        } else {
            break;
        }
    }

    if (value == cur) {
        if (pos) *pos = mid;
        return 1;
    } else {
        if (pos) *pos = min;
        return 0;
    }
}

*/

/* Search for the position of "value". Return 1 when the value was found and
 * sets "pos" to the position of the value within the intset. Return 0 when
 * the value is not present in the intset and sets "pos" to the position
 * where "value" can be inserted. */
method intsetSearch(is: array<int>, value: int) returns (pos: nat, found: bool)
  ensures is.Length > 0 ==> pos <= is.Length
	ensures !found ==> forall k :: 0 <= k < is.Length ==> is[k] != value
	ensures is.Length > 0 && value > is[is.Length-1] ==> pos == is.Length 
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


method intsetRemove(is: array<int>, value: nat) returns (success: bool)
{
    // Since success is actually a pointer passed by reference, 
    // just initialize it as a boolean value for purposes of
    // this method. Initialize as false, which is what the if
    // statement essentially does.
    success := false;
    // Seems 

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