// Reverse function for sequences
function reverse<T>(s: seq<T>): seq<T> {
  if |s| == 0 then [] else reverse(s[1..]) + [s[0]]
}

class Pilha {
  // Concrete representation (array-based)
  var arr: array<int>
  var top: int        // Next available position
  var capacity: int   // Current array size

  // Abstract representation (ghost state)
  ghost var elems: seq<int>

  // Class invariant predicate
  predicate Valid()
    reads this, arr
  {
    capacity == arr.Length &&
    0 <= top <= capacity &&
    elems == CreateSeqFromArray()
  }

  ghost function CreateSeqFromArray(): seq<int>
    reads this, arr
    ensures |CreateSeqFromArray()| == top
    ensures forall i | 0 <= i < top :: CreateSeqFromArray()[i] == arr[i]
  {
    if top == 0 then []
    else CreateSeqFromArray()[..top-1] + [arr[top-1]]
  }

  // Constructor: creates empty stack
  constructor Init()
    ensures Valid() && fresh(arr) && elems == []
  {
    capacity := 10;
    arr := new int[capacity];
    top := 0;
    elems := [];
  }

  // Helper: Resize array when full (private)
  method Resize()
    modifies this
    ensures Valid() && elems == old(elems)
    ensures arr != old(arr) && arr.Length > old(capacity)
  {
    var newCapacity := capacity * 2;
    var newArr := new int[newCapacity];

    // Copy existing elements
    var i := 0;
    while i < top
      invariant 0 <= i <= top
      invariant newArr[..i] == arr[..i]
    {
      newArr[i] := arr[i];
      i := i + 1;
    }

    // Update state
    arr := newArr;
    capacity := newCapacity;
  }

  // Push: Add element to top
  method Push(x: int)
    modifies this
    ensures Valid() && elems == old(elems) + [x]
  {
    if top == capacity {
      Resize();
    }
    arr[top] := x;
    top := top + 1;
    elems := elems + [x];
  }

  // Pop: Remove and return top element
  method Pop() returns (x: int)
    requires !IsEmpty()
    modifies this
    ensures Valid() && elems == old(elems)[..|old(elems)|-1] && x == old(elems)[|old(elems)|-1]
  {
    top := top - 1;
    x := arr[top];
    elems := elems[..|elems|-1];
  }

  // Peek: Return top element without removal
  function Peek(): int
    requires !IsEmpty()
    reads this
    ensures Peek() == elems[|elems|-1]
  {
    arr[top-1]
  }

  // Check if stack is empty
  function IsEmpty(): bool
    reads this
    ensures IsEmpty() == (elems == [])
  {
    top == 0
  }

  // Get number of elements
  function Size(): int
    reads this
    ensures Size() == |elems|
  {
    top
  }

  // Reverse stack elements in-place
  method Reverse()
    modifies this
    ensures Valid() && elems == reverse(old(elems))
  {
    ghost var oldElems := elems;

    var i := 0;
    var j := top - 1;
    while i < j
      invariant 0 <= i <= j < top
      invariant forall k | 0 <= k < i || j < k < top :: arr[k] == oldElems[top-1-k]
      invariant forall k | i <= k <= j :: arr[k] == oldElems[k]
    {
      // Swap elements
      var temp := arr[i];
      arr[i] := arr[j];
      arr[j] := temp;
      i := i + 1;
      j := j - 1;
    }

    // Update abstract state
    elems := reverse(oldElems);
  }

  // Concatenate two stacks (returns new stack)
  method Concat(other: Pilha) returns (res: Pilha)
    requires other.Valid() && Valid()
    ensures res.Valid() && fresh(res.arr)
    ensures res.elems == other.elems + elems
  {
    res := new Pilha.Init();

    // Calculate required capacity
    var totalSize := other.Size() + Size();
    if totalSize == 0 { totalSize := 1; }

    // Create new array
    res.arr := new int[totalSize];
    res.capacity := totalSize;
    res.top := 0;

    // Copy other stack (bottom part)
    var idx := 0;
    while idx < other.top
      invariant 0 <= idx <= other.top
      invariant res.arr[..res.top] == other.arr[..idx]
      invariant res.top == idx
    {
      res.arr[res.top] := other.arr[idx];
      res.top := res.top + 1;
      idx := idx + 1;
    }

    // Copy current stack (top part)
    idx := 0;
    while idx < top
      invariant 0 <= idx <= top
      invariant res.arr[other.top..other.top+res.top] == arr[..idx]
      invariant res.top == other.top + idx
    {
      res.arr[res.top] := arr[idx];
      res.top := res.top + 1;
      idx := idx + 1;
    }

    // Set abstract state
    res.elems := other.elems + elems;
  }
}

// Test/Demonstration method
method Main() {
  // Create and test stack
  var s: Pilha;
  s := new Pilha.Init();

  // Push elements
  s.Push(10);
  s.Push(20);
  s.Push(30);
  assert s.Size() == 3;
  assert s.Peek() == 30;

  // Test pop
  var x := s.Pop();
  assert x == 30;
  assert s.Size() == 2;
  assert s.Peek() == 20;

  // Test isEmpty
  assert !s.IsEmpty();

  // Test reverse
  s.Reverse();
  assert s.Peek() == 10;

  // Create second stack
  var s2: Pilha;
  s2 := new Pilha.Init();
  s2.Push(40);
  s2.Push(50);

  // Test concat
  var s3 := s.Concat(s2);
  assert s3.Size() == 4;
  assert s3.Peek() == 50;
  assert s3.elems == [10, 20, 40, 50];

  // Test empty stack
  var emptyStack: Pilha;
  emptyStack := new Pilha.Init();
  assert emptyStack.IsEmpty();

  print "All tests passed!\n";
}