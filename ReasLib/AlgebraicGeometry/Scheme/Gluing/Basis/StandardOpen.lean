module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.Topology.Sheaves.Basis.Types.Extension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard-open sheaf criteria on the affine-open basis

The criterion is expressed through the generic `BasisCover` and compatible
families API. Names are layered under `Scheme.AffineBasis`, keeping each
public declaration short while exposing the mathematical hierarchy.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Presheaf Opposite TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.AffineBasis

/-- An affine open regarded as an object of the affine-open basis. -/
@[stacks 0F1A "affine-open basis object"]
abbrev obj {X : Scheme.{u}} (U : X.affineOpens) : BasisOpen X.affineOpens :=
  ⟨(U : X.Opens), U.2⟩

/-- The empty affine open regarded as an object of the affine-open basis. -/
@[stacks 0F1A "empty affine-open basis object"]
abbrev emptyObj (X : Scheme.{u}) : BasisOpen X.affineOpens :=
  obj ⟨(⊥ : X.Opens), isAffineOpen_bot X⟩

/-- The two standard opens defined by `f` and `g` have the required union when they cover `U`. -/
@[stacks 0F1A "standard-open basis union"]
theorem standardCover_iUnion_eq
    {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, (U : X.Opens)))
    (hU : (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g) :
    ((obj U).obj : Set X) =
      ⋃ i : ULift.{u} Bool,
        ((obj (X.affineBasicOpen
          (match i.down with | false => f | true => g))).obj : Set X) := sorry

/-- The binary standard-open cover of an affine open defined by two sections. -/
@[stacks 0F1A "binary standard-open basis cover"]
def standardCover
    {X : Scheme.{u}} (U : X.affineOpens) (f g : Γ(X, (U : X.Opens)))
    (hU : (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g) :
    BasisCover X.affineOpens (obj U) where
  ι := ULift.{u} Bool
  obj i := obj (X.affineBasicOpen (match i.down with | false => f | true => g))
  hom _ := ⟨homOfLE (X.basicOpen_le _)⟩
  iUnion_eq := standardCover_iUnion_eq U f g hU

/-- The empty-open part of the binary standard-open gluing condition. -/
@[stacks 0F1A "empty-open gluing condition"]
def StandardGluing.emptyCondition
    {X : Scheme.{u}} (F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)) : Prop :=
  Subsingleton (F.obj (op (emptyObj X))) ∧ Nonempty (F.obj (op (emptyObj X)))

/-- The unique-gluing part of the binary standard-open gluing condition. -/
@[stacks 0F1A "binary standard-open gluing condition"]
def StandardGluing.glueCondition
    {X : Scheme.{u}} (F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)) : Prop :=
  ∀ (U : X.affineOpens) (f g : Γ(X, (U : X.Opens)))
    (hU : (U : X.Opens) = X.basicOpen f ⊔ X.basicOpen g),
    (standardCover U f g hU).HasUniqueGluing F

/-- The affine-basis sheaf condition reduced to the empty open and binary standard-open covers. -/
@[stacks 0F1A "standard-open gluing criterion"]
def StandardGluing
    {X : Scheme.{u}} (F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)) : Prop :=
  StandardGluing.emptyCondition F ∧ StandardGluing.glueCondition F

namespace StandardGluing

/-- The empty-open condition supplied by the combined gluing predicate. -/
@[stacks 0F1A "empty-open condition projection"]
theorem empty {X : Scheme.{u}}
    {F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)}
    (h : StandardGluing F) : emptyCondition F := sorry

/-- The binary-gluing condition supplied by the combined gluing predicate. -/
@[stacks 0F1A "binary-gluing condition projection"]
theorem glue {X : Scheme.{u}}
    {F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)}
    (h : StandardGluing F) : glueCondition F := sorry

/-- The combined predicate is equivalent to its empty-open and gluing components. -/
@[stacks 0F1A "standard-open gluing iff"]
theorem iff {X : Scheme.{u}}
    (F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)) :
    StandardGluing F ↔ emptyCondition F ∧ glueCondition F := sorry

/-- Empty-open and binary-gluing conditions construct the combined predicate. -/
@[stacks 0F1A "standard-open gluing constructor"]
theorem of_empty_of_glue
    {X : Scheme.{u}}
    {F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)}
    (hempty : emptyCondition F) (hglue : glueCondition F) : StandardGluing F := sorry

end StandardGluing

/-- The canonical extension of a sheaf on the induced affine-open basis site, retaining the
comparison isomorphism after restriction to affine opens. -/
@[stacks 0F1A "canonical affine-basis extension"]
noncomputable def extension
    {X : Scheme.{u}}
    (F : BasisSiteSheaf (Type (max u v)) X.affineOpens) :
    BasisPresheaf.Extension F.presheaf where
  sheaf := F.extend X.isBasis_affineOpens
  restrictIso := F.restrictExtendIso X.isBasis_affineOpens

/-- A presheaf on the affine-open basis extends to a sheaf on the whole scheme exactly when it
is a sheaf on that basis. Isomorphism is the invariant extension notion. -/
@[stacks 0F1A "extension from the affine-open basis"]
theorem exists_sheaf_iff_isBasisSheaf
    {X : Scheme.{u}}
    (F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)) :
    (∃ G : TopCat.Sheaf (Type (max u v)) X,
      IsIsomorphic ((basisOpenInclusion X.affineOpens).op ⋙ G.presheaf) F) ↔
      Presheaf.IsBasisSheaf F := sorry

/-- The affine-open basis sheaf condition is detected by empty-open and binary standard-open
gluing. -/
@[stacks 0F1A]
theorem isBasisSheaf_iff_standardGluing
    {X : Scheme.{u}}
    (F : (BasisOpen X.affineOpens)ᵒᵖ ⥤ Type (max u v)) :
    Presheaf.IsBasisSheaf F ↔ StandardGluing F := sorry

end AlgebraicGeometry.Scheme.AffineBasis
