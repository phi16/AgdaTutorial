{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Revise.IO where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified Control.Exception
import qualified Data.Text
import qualified Data.Text.IO
import qualified MAlonzo.RTE
import qualified System.IO
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Coinduction
import qualified MAlonzo.Code.Agda.Builtin.IO
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Data.Colist
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.IO.Primitive

name4 = "Revise.IO.char[a]"
d4 = 'a'
name6 = "Revise.IO.string[hello]"
d6 = coe Data.Text.pack "hello"
name8 = "Revise.IO.unlines"
d8 v0
  = case coe v0 of
      [] -> coe Data.Text.pack ""
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d6 v1
             (coe
                MAlonzo.Code.Data.String.Base.d6 (coe Data.Text.pack "\n")
                (coe d8 v2))
      _ -> coe MAlonzo.RTE.mazUnreachableError
main = d14
name14 = "Revise.IO.main"
d14
  = coe
      MAlonzo.Code.IO.Primitive.d30
      (coe
         MAlonzo.Code.Data.String.d12 (coe Data.Text.pack "Hello World!"))
name16 = "Revise.IO.main\8242"
d16 = coe MAlonzo.Code.IO.Primitive.d8 () erased erased
name18 = "Revise.IO.getLine"
d18 ::
  (MAlonzo.Code.Agda.Builtin.IO.AgdaIO () (MAlonzo.Code.Data.Colist.AgdaColist () Char))
d18 = getLine
name20 = "Revise.IO.main\8243"
d20
  = coe
      MAlonzo.Code.IO.Primitive.d18 () () erased erased d18
      MAlonzo.Code.IO.Primitive.d30
name22 = "Revise.IO.main\8244"
d22
  = coe
      MAlonzo.Code.IO.Primitive.d18 () () erased erased d18
      (\ v0 ->
         coe
           MAlonzo.Code.IO.Primitive.d30
           (coe
              MAlonzo.Code.Data.Colist.du222 ()
              (coe MAlonzo.Code.Data.String.d12 (coe Data.Text.pack "Hello "))
              v0))
name26 = "Revise.IO.echo"
d26
  = coe
      MAlonzo.Code.IO.Primitive.d18 () () erased erased d18
      (\ v0 ->
         let v1 = coe MAlonzo.Code.IO.Primitive.d30 v0 in
         case coe v0 of
           [] -> coe MAlonzo.Code.IO.Primitive.d8 () erased erased
           _ -> v1)
name32 = "Revise.IO.f"
d32 v0 v1 v2
  = case coe v1 of
      []
        -> case coe v2 of
             [] -> coe v2
             (:) v3 v4
               -> let v5 = coe (:) v3 (coe d123 v0 v3 v4) in
                  case coe v3 of
                    '\n' -> coe (:) '\n' (coe d79 v0 v4)
                    _ -> coe v5
             _ -> coe MAlonzo.RTE.mazUnreachableError
      (:) v3 v4 -> coe (:) v3 (coe du175 v0 v4 v2)
      _ -> coe MAlonzo.RTE.mazUnreachableError
name54 = "Revise.IO.trans"
d54 = coe d32 [] []
name56 = "Revise.IO.main\8279"
d56
  = coe
      MAlonzo.Code.IO.Primitive.d18 () () erased erased
      MAlonzo.Code.IO.Primitive.d20
      (\ v0 -> coe MAlonzo.Code.IO.Primitive.d28 (coe d54 v0))
name79 = "Revise.IO._.\9839-0"
d79 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe
         d32 []
         (coe
            MAlonzo.Code.Data.List.Base.du18
            (coe MAlonzo.Code.Data.List.Base.du234 v0) (coe (:) '\n' []))
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v1))
name123 = "Revise.IO._.\9839-1"
d123 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.d16
      (coe
         d32 (coe (:) v1 v0) []
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d22 v2))
name175 = "Revise.IO._.\9839-2"
d175 v0 v1 v2 v3 = du175 v0 v2 v3
du175 v0 v1 v2
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.d16 (coe d32 v0 v1 v2)