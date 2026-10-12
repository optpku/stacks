/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Stability
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Faithful
import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# Full faithfulness of pullback for scheme descent data

Pullback on singleton-family scheme descent data is fully faithful along an fpqc covering
morphism, and also along any morphism whose domain covers the common base fpqc-locally.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

/-- Pullback on singleton-family descent data along an fpqc covering over a common base is
fully faithful. -/
theorem fullyFaithful {X X' S : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S)
    (f : X' ⟶ X) (sq : CommSq f a' a (𝟙 S))
    (hfpqc : Scheme.FpqcCovering (fun _ : Unit ↦ Over.mk f)) :
    Nonempty (functor a a' (𝟙 S) f sq).FullyFaithful := sorry

/-- Pullback on singleton-family descent data along a morphism over a common base is fully
faithful when the domain structure morphism is an fpqc covering. -/
theorem fullyFaithfulOfFpqcDomain {X X' S : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S)
    (f : X ⟶ X') (sq : CommSq f a a' (𝟙 S))
    (hfpqc : Scheme.FpqcCovering (fun _ : Unit ↦ Over.mk a)) :
    Nonempty (functor a' a (𝟙 S) f sq).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.DescentData.Pullback
