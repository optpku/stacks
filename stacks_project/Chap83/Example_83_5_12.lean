module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.FormalDisk
import StacksCheckRecall

/-!
# Morphisms that agree on field-valued points but fail to be invariant

The formal disk and the punctured-negation quotient of the affine line are reduced
quasi-separated algebraic spaces. Their coordinate-induced morphisms agree on all
field-valued points but are unequal, giving a set-theoretically invariant morphism
that is not invariant. Thus quasi-separatedness cannot replace local separatedness
in Lemma 83.5.11.
-/

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Example 83.5.12 (1): The coordinate and negative-coordinate maps from the formal disk to the involution
quotient agree after pullback along every field-valued point. -/
@[stacks 048Z] #check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.eq_on_fieldValuedPoints :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] (σ : Spec (.of K) ⟶ base k)
    (p : Over.mk σ ⟶ formalDisk k),
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map p ≫ fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map p ≫
        fromDiskNeg k)

/- Example 83.5.12 (2): The coordinate and negative-coordinate maps from the formal disk to the involution
quotient are unequal. -/
@[stacks 048Z] #check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.fromDisk_ne_fromDiskNeg :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    fromDisk k ≠ fromDiskNeg k)

/- Example 83.5.12 (3): Every geometric point of the formal disk equalizes the identity and negation
after postcomposition with the coordinate-induced map to the involution quotient. -/
@[stacks 048Z] #check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.eq_on_geometricPoints :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)]
    (K : Type u) [Field K] [IsAlgClosed K] (σ : Spec (.of K) ⟶ base k)
    (p : Over.mk σ ⟶ formalDisk k),
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (p ≫ (involutionPreRelation k).s) ≫ fromDisk k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (p ≫ (involutionPreRelation k).t) ≫ fromDisk k)

/- Example 83.5.12 (4): The identity and negation on the formal disk induce unequal morphisms after
postcomposition with the coordinate-induced map to the involution quotient. -/
@[stacks 048Z] #check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.not_t_fromDisk_eq_s_fromDisk :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (involutionPreRelation k).t ≫ fromDisk k ≠
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
        (involutionPreRelation k).s ≫ fromDisk k)

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.isReduced_sheafOfPoints :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    ∃ (U : Over (base k))
      (p : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶
        sheafOfPoints k),
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) p.hom ∧
          AlgebraicGeometry.IsReduced U.left)

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.formalDiskNeg_comp :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (formalDiskNeg k) ≫
      fromDisk k =
      fromDiskNeg k)

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.sheafOfPoints_spec :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj))

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.quasiCompact_diag_sheafOfPoints :
  ∀ (k : Type u) [Field k] [NeZero (2 : k)],
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k).obj))

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.instIsReduced_formalDisk :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AlgebraicSpace.IsReduced
      (AlgebraicGeometry.AlgebraicSpace.ofOver (formalDisk k)))

#check (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.instIsQuasiSeparated_formalDisk :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.AlgebraicSpace.IsQuasiSeparated
      (AlgebraicGeometry.AlgebraicSpace.ofOver (formalDisk k)))
