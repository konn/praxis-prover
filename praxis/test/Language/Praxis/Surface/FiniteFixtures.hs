{-# LANGUAGE OverloadedStrings #-}

module Language.Praxis.Surface.FiniteFixtures (finitePrelude, finiteOrdinals, finiteProtocol, boolInstance) where

import Data.Text (Text)
import Data.Text qualified as T

finitePrelude :: Text
finitePrelude = finiteOrdinals <> finiteProtocol <> boolInstance

finiteOrdinals :: Text
finiteOrdinals =
  T.unlines
    [ "data Fin (n : Nat) where"
    , "  FZero : {n : Nat} -> Fin (S n)"
    , "  FSucc : {n : Nat} -> Fin n -> Fin (S n)"
    , "rank : Fin n -> Nat"
    , "rank FZero = 0"
    , "rank (FSucc i) = S (rank i)"
    , "bounded : (i : Fin n) -> rank i < n"
    , "bounded FZero = rfl"
    , "bounded (FSucc i) = bounded i"
    , "from-nat : {k n : Nat} -> k < n -> Fin n"
    , "from-nat {0} {S n} h = FZero"
    , "from-nat {S k} {S n} h = FSucc (from-nat {k} {n} h)"
    , "from-nat {k} {0} h = absurd h"
    , "to-from : {k n : Nat} -> k < n -> rank (from-nat {k} {n} (by assumption)) = k"
    , "to-from {0} {S n} h = rfl"
    , "to-from {S k} {S n} h = by"
    , "  have ih := to-from {k} {n}"
    , "  cong"
    , "to-from {k} {0} h = absurd h"
    , "from-to : (i : Fin n) -> from-nat {rank i} {n} (bounded i) = i"
    , "from-to FZero = rfl"
    , "from-to (FSucc i) = by"
    , "  have ih := from-to i"
    , "  cong"
    , "{-# BUILTIN FIN Fin #-}"
    , "{-# BUILTIN FIN_FROM_NAT from-nat #-}"
    , "{-# BUILTIN FIN_TO_NAT rank #-}"
    , "{-# BUILTIN FIN_TO_NAT_BOUND bounded #-}"
    , "{-# BUILTIN FIN_FROM_TO_NAT from-to #-}"
    , "{-# BUILTIN FIN_TO_FROM_NAT to-from #-}"
    ]

finiteProtocol :: Text
finiteProtocol =
  T.unlines
    [ "class Finite a where"
    , "  card : Nat"
    , "  code : a -> Fin card"
    , "  decode : Fin card -> a"
    , "  decode-code : (x : a) -> decode (code x) = x"
    , "{-# BUILTIN FINITE Finite #-}"
    , "{-# BUILTIN FINITE_CARD Finite.card #-}"
    , "{-# BUILTIN FINITE_CODE Finite.code #-}"
    , "{-# BUILTIN FINITE_DECODE Finite.decode #-}"
    , "{-# BUILTIN FINITE_DECODE_CODE Finite.decode-code #-}"
    ]

boolInstance :: Text
boolInstance =
  T.unlines
    [ "data Bool = False | True"
    , "bool-from-nat : Nat -> Bool"
    , "bool-from-nat 0 = False"
    , "bool-from-nat (S k) = True"
    , "instance Finite Bool where"
    , "  card = 2"
    , "  code False = FZero {1}"
    , "  code True = FSucc (FZero {0})"
    , "  decode i = bool-from-nat (rank i)"
    , "  decode-code False = rfl"
    , "  decode-code True = rfl"
    ]
