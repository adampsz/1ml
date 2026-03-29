  $ ./FOmega.exe ./FOmega.txt
  
  0. Hello
  
  (FOmega.Value.VConst (Common.Const.CInt 9))
  (FOmega.Value.VConst (Common.Const.CInt 2)) ::
    (FOmega.Type.TPrim Common.Prim.PInt)
  
  1. Pairs (Record encoding)
  
  (FOmega.Value.VConst (Common.Const.CInt 6))
  (FOmega.Value.VConst (Common.Const.CBool true))
  (FOmega.Value.VConst (Common.Const.CUnit ())) ::
    (FOmega.Type.TPrim Common.Prim.PUnit)
  
  2. Pairs (Church encoding)
  
  (FOmega.Value.VConst (Common.Const.CInt 6))
  (FOmega.Value.VConst (Common.Const.CBool true))
  (FOmega.Value.VConst (Common.Const.CUnit ())) ::
    (FOmega.Type.TPrim Common.Prim.PUnit)
  
  3. Lists (right fold encoding)
  
   - Basics
  (FOmega.Value.VConst (Common.Const.CInt 15))
  (FOmega.Value.VConst (Common.Const.CInt 4))
  (FOmega.Value.VConst (Common.Const.CBool false))
  (FOmega.Value.VConst (Common.Const.CBool true))
   - Mapped
  (FOmega.Value.VConst (Common.Const.CInt 24))
  (FOmega.Value.VConst (Common.Const.CInt 7))
  (FOmega.Value.VConst (Common.Const.CInt 8))
  (FOmega.Value.VConst (Common.Const.CInt 9))
   - Append
  (FOmega.Value.VConst (Common.Const.CInt 9))
  (FOmega.Value.VConst (Common.Const.CInt 8))
  (FOmega.Value.VConst (Common.Const.CInt 7))
  (FOmega.Value.VConst (Common.Const.CInt 6))
  (FOmega.Value.VConst (Common.Const.CInt 5))
  (FOmega.Value.VConst (Common.Const.CInt 4))
   - Nested
  (FOmega.Value.VConst (Common.Const.CInt 3))
  (FOmega.Value.VConst (Common.Const.CInt 2))
  (FOmega.Value.VConst (Common.Const.CInt 1))
  (FOmega.Value.VConst (Common.Const.CUnit ())) ::
    (FOmega.Type.TPrim Common.Prim.PUnit)
  
  4. Church numerals
  
  (FOmega.Value.VConst (Common.Const.CInt 4))
  (FOmega.Value.VConst (Common.Const.CInt 7))
  (FOmega.Value.VConst (Common.Const.CInt 12))
  (FOmega.Value.VConst (Common.Const.CInt 81))
  (FOmega.Value.VConst (Common.Const.CInt 1))
  (FOmega.Value.VConst (Common.Const.CInt 54))
  (FOmega.Value.VConst (Common.Const.CUnit ())) ::
    (FOmega.Type.TPrim Common.Prim.PUnit)
