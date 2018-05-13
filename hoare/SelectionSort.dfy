/**
 * This is to demonstrate the hoare logic used in our Coq script is similar to
 * Dafny.
 */

method selectionsort(a : array<int>)
  requires a != null
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x, y :: 0 <= x < i <= y < n ==> a[x] <= a[y]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := i + 1;
    var best := i;
    while j < n
      invariant 0 <= i < j <= n
      invariant i <= best < n
      invariant forall k :: i <= k < j ==> a[best] <= a[k]
      invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
      invariant forall x, y :: 0 <= x < i <= y < n ==> a[x] <= a[y]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] < a[best] {
        best := j;
      }
      j := j + 1;
    }
    var tmp := a[best];
    a[best] := a[i];
    a[i] := tmp;
    i := i + 1;
  }
}
