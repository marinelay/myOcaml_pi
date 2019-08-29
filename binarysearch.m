@ 0 <= l and u < |a| and forall i,j. ((l<= i and i <= j and j<=u) -> a[i] <= a[j])
@ exist i. (l<=i and i<=u and a[i] = e)

T : (u-l+1) | (u-l+1) >= 0 

BinarySearch (int a[], int l, int u, int e) {
    if (l > u) { return false;}
    else {
        int m := (l + u) / 2;
        if (a[m] = e) {
            return true;
        }
        else {
            if (a[m] < e) { 
                return BinarySearch(a, (m+1), u, e);
            }
            else {
                return BinarySearch(a, l, (m-1), e);
            }
        }
    }
}