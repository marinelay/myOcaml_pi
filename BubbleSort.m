@ |a|>=0 @ forall i,j. ((0<=i and i<=j and j<=(|a|-1)) -> a[i] <= a[j])
T : None
BubbleSort (int a[], int i, int j, int t) {
    @ (0-1) <= i and i < |a|
    and forall x,y. ((0<=x and x <= i and i<(i+1) and (i+1)<=y and y<=(|a|-1)) -> a[x] <= a[y]) 
    and forall x,y. ((i<=x and x<=y and y<=(|a|-1)) -> a[x] <= a[y])

    T : (i+1, i+1) | (i+1)>=0

    for (int i:= (|a|-1); i>0; int i := (i-1)) {

        @ 1 <= i and i < |a| and 0 <= j and j<=i
        and forall x,y. ((0<=x and x <= i and i<(i+1) and (i+1)<=y and y<=(|a|-1)) -> a[x] <= a[y]) 
        and forall x,y. ((0<=x and x <= (j-1) and (j-1)<j and j<=y and y<=j) -> a[x] <= a[y]) 
        and forall x,y. ((i<=x and x<=y and y<=(|a|-1)) -> a[x] <= a[y])

        T : (i+1, i-j) | (i+1)>=0 and (i-j)>=0

        for (int j := 0; j<i; int j := j+1) {
            if(a[j] > a[j+1]) {
                int t := a[j];
                int a[j] := a[j+1];
                int a[j+1] := t;
            }
        }
    }

    return true;
}