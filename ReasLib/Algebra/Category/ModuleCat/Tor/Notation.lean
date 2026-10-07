module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Notation for Module `Tor`

This leaf owns stable notation for the degree-`n` `Tor` object of two modules over a commutative
ring.  It is independent of Chapter 10 and of any particular exact-sequence presentation.

@stack 0H7P
-/

@[expose] public section

open CategoryTheory

-- The parenthesized degree follows the scoped derived `Ext⁽n⁾` notation.
set_option quotPrecheck false in
scoped[ModuleTor] notation:max "Tor⁽" n "⁾[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) n).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

-- Retain the common degree-one spelling as a compact specialization.
set_option quotPrecheck false in
notation "Tor₁[" R "](" M ", " N ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))
