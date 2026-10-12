/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- An `R`-module is pure projective when its covariant represented Hom functor sends every
universally exact short complex to a short exact complex. -/
def PureProjective (P : ModuleCat.{v} R) : Prop :=
  ∀ S : ShortComplex (ModuleCat.{v} R), S.UniversallyExact →
    (S.map (preadditiveCoyonedaObj P)).ShortExact

/-- A module is pure projective exactly when its covariant represented Hom functor sends every
universally exact short complex to a short exact complex. -/
theorem pureProjective_iff_map_shortExact (P : ModuleCat.{v} R) :
    P.PureProjective ↔
      ∀ S : ShortComplex (ModuleCat.{v} R), S.UniversallyExact →
        (S.map (preadditiveCoyonedaObj P)).ShortExact := sorry

/-- An `R`-module is pure injective when its contravariant represented Hom functor sends every
universally exact short complex to a short exact complex in the reverse direction. -/
def PureInjective (I : ModuleCat.{v} R) : Prop :=
  ∀ S : ShortComplex (ModuleCat.{v} R), S.UniversallyExact →
    (S.op.map (preadditiveYonedaObj I)).ShortExact

/-- A module is pure injective exactly when its contravariant represented Hom functor sends every
universally exact short complex to a short exact complex in the reverse direction. -/
theorem pureInjective_iff_map_shortExact (I : ModuleCat.{v} R) :
    I.PureInjective ↔
      ∀ S : ShortComplex (ModuleCat.{v} R), S.UniversallyExact →
        (S.op.map (preadditiveYonedaObj I)).ShortExact := sorry

end ModuleCat
