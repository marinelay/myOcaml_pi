@ true @ forall i,j. ((0<=i and i<=j and j<=(|a|-1)) -> a[i] <= a[j])
BubbleSort (int a[]) {
    @ forall x,y. (0<=x and x<=i and i<(i+1) and (i+1)<=y and y<=(|a|-1))
    
    for (int i:= (|a|-1); i>0; int i := (i-1)) {
        return false;
    }

    return true;
}