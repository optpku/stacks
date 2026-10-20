module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Flat
public import ReasLib.CategoryTheory.Sites.Grothendieck.Fiberwise

/-!
# Lemma 85.11.1

A morphism from a ringed simplicial total site is flat if and only if every
canonical component is flat, for both total-site presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite

universe u v w uD vD

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsSiteDiagram C J] (O : Sheaf (topology C J) RingCat.{w})
variable {D : RingedSite.{uD, vD, w}}
variable [UnivLE.{max u v, w}]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable (a : ToposHom (totalRingedSite C J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (augmentationComponent C J O a n).structureMap).IsRightAdjoint]

/- Lemma 85.11.1. Flatness is equivalent to flatness of all degree components
for the continuous-diagram total site. -/
@[stacks 0DH3] #check (CategoryTheory.SimplicialSites.augmentation_isFlat_iff C J O a :
  ToposHom.IsFlat a ↔
    ∀ n : SimplexCategory, ToposHom.IsFlat (augmentationComponent C J O a n))

end CategoryTheory.SimplicialSites

section Fiberwise

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [Grothendieck.IsFiberwiseSite F J]
variable (O : Sheaf (Grothendieck.precoverage F J).toGrothendieck RingCat.{w})
variable {D : RingedSite.{uD, vD, w}}
variable [UnivLE.{max u v, w}]
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [GrothendieckTopology.HasSheafCompose
    (Grothendieck.precoverage F J).toGrothendieck (forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (Grothendieck.ι F (op n)).IsContinuous (J (op n)).toGrothendieck
      (Grothendieck.precoverage F J).toGrothendieck]
variable [∀ n : SimplexCategory,
    (Grothendieck.ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck
      (Grothendieck.precoverage F J).toGrothendieck]
variable [∀ n : SimplexCategory,
    ((J (op n)).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n : SimplexCategory, HasSheafify (J (op n)).toGrothendieck (Type w)]
variable [∀ n : SimplexCategory, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι F (op n)).op.HasPointwiseRightKanExtension P]
variable (a : ToposHom (ofRingSheaf (Grothendieck.precoverage F J).toGrothendieck O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory, Functor.IsRightAdjoint (SheafOfModules.restrictScalars.{w}
    ((Cocontinuous.restrictionMorphism
      (ofRingSheaf (Grothendieck.precoverage F J).toGrothendieck O)
      (J (op n)).toGrothendieck (Grothendieck.ι F (op n))).comp a).structureMap)]

/- Lemma 85.11.1. Flatness is equivalent to flatness of all degree components
for the fiberwise Grothendieck total site. -/
@[stacks 0DH3] #check (RingedSite.ToposHom.isFlat_iff_restrictions
  (ofRingSheaf (Grothendieck.precoverage F J).toGrothendieck O)
  (fun n : SimplexCategory ↦ F.obj (op n))
  (fun n ↦ (J (op n)).toGrothendieck)
  (fun n ↦ Grothendieck.ι F (op n))
  (fun totalObject ↦ ⟨totalObject.base.unop, totalObject.fiber, rfl⟩) a :
  ToposHom.IsFlat a ↔ ∀ n : SimplexCategory,
    ToposHom.IsFlat ((Cocontinuous.restrictionMorphism
      (ofRingSheaf (Grothendieck.precoverage F J).toGrothendieck O)
      (J (op n)).toGrothendieck (Grothendieck.ι F (op n))).comp a))

end Fiberwise
