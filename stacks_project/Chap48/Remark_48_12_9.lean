/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Duality.Rigidity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Remark 48.12.9: The isomorphism `relativeDualizingComplexIso` expresses a rigidity
phenomenon: its left-hand side depends linearly on the relative dualizing complex,
whereas its right-hand side depends quadratically on it. -/
@[stacks 0BRU] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingComplexIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      [CompactSpace Y] → [QuasiSeparatedSpace Y] → [IsProper f] → [Flat f] →
      [Scheme.Hom.FinitePresentation f] →
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) →
      (c : DerivedQCoh (CategoryTheory.Limits.pullback f f) ⥤ DerivedQCoh X) →
      (pushforwardCohomologyIn f ⊣ a) →
      (pushforwardCohomologyIn (pullback.diagonal f) ⊣ c) →
      IsIsomorphic (a.obj (structureSheaf Y))
        (c.obj (tensorObj
          ((pullback (pullback.fst f f)).obj (a.obj (structureSheaf Y)))
          ((pullback (pullback.snd f f)).obj (a.obj (structureSheaf Y))))))

end AlgebraicGeometry.Scheme.DerivedQCoh
