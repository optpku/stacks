/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Remark_61_10_4_Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open Scheme.Over
open Extension

universe u w

/- Remark 61.10.4 (1): if `S` lies in a big site `Sch_h` and `F` is an
h-sheaf of sets on `(Sch/S)_h` such that `F(T) = colim F(T_i)` whenever
`T = lim T_i` is a directed limit of affine schemes in `(Sch/S)_h`, then
`F` extends uniquely to a functor `F'` on all schemes over `S` such that
(a) `F'` is an h-sheaf and (b) `F'` is limit preserving.
See More on Flatness, Lemma 38.35.4. -/
@[stacks 0EVR] #check
  (existsUniqueHSheafExtension :
    ∀ {S : Scheme.{u}} (C : ObjectProperty (Over S))
      (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1)),
      ContainsAffineOpens C → ContainsFinitelyPresentedAffines C →
      Presheaf.IsSheaf
          (C.ι.restrictedTopology ((Scheme.hPrecoverage.toGrothendieck).over S)) F →
        PreservesDirectedAffineLimits C F →
          ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (eF' : C.ι.op ⋙ F' ≅ F),
            ∃ (_ : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F'),
            ∃ (_ : Scheme.Over.PreservesDirectedAffineLimits S F'),
              ∀ (G : (Over S)ᵒᵖ ⥤ Type (u + 1)) (eG : C.ι.op ⋙ G ≅ F),
                Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) G →
                Scheme.Over.PreservesDirectedAffineLimits S G →
                ∃! α : F' ≅ G, Functor.isoWhiskerLeft C.ι.op α ≪≫ eG = eF')

/- Remark 61.10.4 (2): in this situation the unique h-sheaf limit-preserving
extension `F'` satisfies the sheaf property for the V topology.
See Lemma 61.10.3. -/
@[stacks 0EVR] #check
  (existsHSheafExtension_satisfiesVSheafProperty :
    ∀ {S : Scheme.{u}} (C : ObjectProperty (Over S))
      (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1)),
      ContainsAffineOpens C → ContainsFinitelyPresentedAffines C →
      Presheaf.IsSheaf
          (C.ι.restrictedTopology ((Scheme.hPrecoverage.toGrothendieck).over S)) F →
        PreservesDirectedAffineLimits C F →
          ∃ (F' : (Over S)ᵒᵖ ⥤ Type (u + 1)), ∃ (_ : C.ι.op ⋙ F' ≅ F),
            ∃ (_ : Presheaf.IsSheaf ((Scheme.hPrecoverage.toGrothendieck).over S) F'),
            ∃ (_ : Scheme.Over.PreservesDirectedAffineLimits S F'),
              satisfiesVSheafProperty.{u, u + 1, w} S F')
