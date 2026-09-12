{-# LANGUAGE QuasiQuotes #-}

module Language.Praxis.PRA.Lemmas (
  lemmas,
  succSubSucc,
  ltSucc,
  succLtSuccIffLt,
  zeroMinus,
  ltZeroIsZero,
  unfoldSuccLtSucc,
  zeroLtSucc,
) where

import Language.Praxis.PRA.Tactic.Quote

[pra|
library lemmas

theorem succSubSucc : |- S n - S m = n - m
by
  induction m
  { 
    Defeq (S n - 1) (n - 0);
    Id
  }
  {
    Defeq (S n - S (S m')) (prd (S n - S m'));
    rewrite (S n - S m' = n - m') in (S n - S (S m') = prd (S n - S m'));
    Defeq (prd (n - m')) (n - S m');
    rewrite (prd (n - m') = n - S m') in (S n - S (S m') = prd (n - m'));
    Id
  }

theorem ltSucc : |- t < S t
by
  induction t as n
  { Defeq (0 < 1) 1; Id }
  {
    have H: (S (S n) - S n = S n - n)
      { exact succSubSucc };
    calc
      (S n < S (S n))
        = sgn (S (S n) - S n)
        = sgn (S n - n)
          by cong H
        = (n < S n)
        = 1
          by exact H1
  }

theorem succLtSuccIffLt  : |- (t < u) = (S t < S u)
by 
  Defeq (S t < S u) (sgn (S u - S t));
  have H: (S u - S t = u - t) { exact succSubSucc };
  symmetry H as H5;
  calc
    (t < u)
      = sgn (u - t)
      = sgn (S u - S t)    by cong H5
      = (S t < S u)

theorem zeroMinus : |- 0 - t = 0
by
  induction t as n
  {
    calc (0 - 0) = 0
  }
  {
    calc (0 - S n)
    = prd (0 - n)
    = prd 0 by cong H1
    = 0
  }

theorem ltZeroIsZero: |- (t < 0) = 0
by
  have H: (0 - t = 0) { exact zeroMinus };
  calc
    (t < 0)
    = sgn (0 - t)
    = sgn 0
      by cong H
    = 0

theorem unfoldSuccLtSucc : |- (S t < S u) = (t < u)
by have H: ((t < u) = (S t < S u)) { exact succLtSuccIffLt };
   symmetry H as H2;
   exact H2

theorem zeroLtSucc : |- 0 < S t
by refl

|]