Step_read/local.get x {
 Push $local(z, x)
}


Step_pure/local.tee x {
 Assert (top_value())
 Pop val
 Push val
 Push val
 Execute (LOCAL.SET x)
}

Step/local.set x {
 Assert (top_value())
 Pop val
 $with_local(z, x, val)
}

with_local (s, f) x v {
 f.LOCALS[x] := v
}

local (s, f) x {
 Return f.LOCALS[x]
}

Let f = { LOCALS: []; MODULE: moduleinst; }
