# Partial jq stdlib, as much of it that is currently implemented

def map(f): [.[] | f];
def select(f): if f then . else empty end;
