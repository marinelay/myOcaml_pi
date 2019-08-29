@ 0 <= l @ exist i.(l<=i and i<=u and a[i] = e)
T : None

LinearSearch (int a[], int l, int u, int e, int i ) 
{ 
    @ l <= i and forall j. ((l<=j and j<i) -> a[j] != e)
    T : (u-i) | (u-i) >= 0

    for (int i := l; i<=u; int i := i+1) {
        if (a[i] = e) { return true; }
    }

    return false;

}