module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k]

namespace RationalTail

/-- The ideal sheaf of a selected reduced irreducible component. -/
noncomputable def componentIdeal (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : X.left.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (X.left.irreducibleComponentClosed Z)

/-- The scheme-theoretic closure ideal of the open complement of a component. -/
noncomputable def complementIdeal (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : X.left.IdealSheafData :=
  schemeTheoreticClosureIdeal (componentIdeal X Z).openComplement

/-- The scheme-theoretic intersection of a component and the closure of its complement. -/
noncomputable abbrev intersection (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : Scheme :=
  Scheme.schemeTheoreticIntersection (componentIdeal X Z) (complementIdeal X Z)

/-- The selected component, regarded as a scheme over the base field. -/
noncomputable abbrev componentOver (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk ((componentIdeal X Z).subschemeι ≫ X.hom)

/-- The closure of the open complement, regarded as a scheme over the base field. -/
noncomputable abbrev complementOver (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk ((complementIdeal X Z).subschemeι ≫ X.hom)

/-- The canonical map from the intersection into the selected component. -/
noncomputable abbrev toComponent (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    intersection X Z ⟶ (componentIdeal X Z).subscheme :=
  Scheme.IdealSheafData.inclusion (le_sup_left : componentIdeal X Z ≤
    componentIdeal X Z ⊔ complementIdeal X Z)

/-- The canonical map from the intersection into the complementary closure. -/
noncomputable abbrev toComplement (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    intersection X Z ⟶ (complementIdeal X Z).subscheme :=
  Scheme.IdealSheafData.inclusion (le_sup_right : complementIdeal X Z ≤
    componentIdeal X Z ⊔ complementIdeal X Z)

/-- The scheme-theoretic intersection, regarded as a scheme over the base field. -/
noncomputable abbrev intersectionOver (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk (toComponent X Z ≫ (componentIdeal X Z).subschemeι ≫ X.hom)

/-- Evaluation of component global functions at a point of the intersection. -/
noncomputable def attachmentEvaluation (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) (x : intersection X Z) :
    Γ((componentIdeal X Z).subscheme, ⊤) →+*
      (intersection X Z).residueField x :=
  ((toComponent X Z).residueFieldMap x).hom.comp
    ((componentIdeal X Z).subscheme.Γevaluation ((toComponent X Z) x)).hom

/-- The ring equivalence induced by bijective evaluation at an intersection point. -/
noncomputable def evaluationEquiv (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) (x : intersection X Z)
    (h_eval : Function.Bijective (attachmentEvaluation X Z x)) :
    Γ((componentIdeal X Z).subscheme, ⊤) ≃+* (intersection X Z).residueField x :=
  RingEquiv.ofBijective (attachmentEvaluation X Z x) h_eval

/-- The underlying ring homomorphism of the evaluation equivalence is evaluation. -/
theorem evaluationEquiv_toRingHom (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) (x : intersection X Z)
    (h_eval : Function.Bijective (attachmentEvaluation X Z x)) :
    (evaluationEquiv X Z x h_eval).toRingHom = attachmentEvaluation X Z x := sorry

/-- The canonical map from the selected component to the complementary closure. -/
noncomputable def canonicalCollapse (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) (x : intersection X Z)
    (h_eval : Function.Bijective (attachmentEvaluation X Z x)) :
    (componentIdeal X Z).subscheme ⟶ (complementIdeal X Z).subscheme :=
  (componentIdeal X Z).subscheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (evaluationEquiv X Z x h_eval).symm.toRingHom) ≫
    (intersection X Z).fromSpecResidueField x ≫
    toComplement X Z

end RationalTail

open RationalTail

/-- The explicit data defining a rational tail on a scheme over a field. -/
structure RationalTail (X : SchemeOverField k) where
  /-- The selected irreducible component. -/
  component : irreducibleComponents X.left
  /-- The attachment point in the scheme-theoretic intersection. -/
  attachment : intersection X component
  /-- The attachment point is closed in the scheme-theoretic intersection. -/
  attachment_closed : attachment ∈ closedPoints (intersection X component)
  /-- The scheme-theoretic closure of the complement is nonempty. -/
  complement_nonempty : Nonempty (complementIdeal X component).subscheme
  /-- The attachment point is the unique point of the intersection. -/
  intersection_unique : ∀ y : intersection X component, y = attachment
  /-- The scheme-theoretic intersection is reduced. -/
  intersection_reduced : IsReduced (intersection X component)
  /-- Component global functions evaluate bijectively at the attachment. -/
  evaluation_bijective : Function.Bijective (attachmentEvaluation X component attachment)
  /-- The first cohomology of the component structure sheaf vanishes. -/
  genus_zero : Scheme.Hom.cohomologyFinrank (componentOver X component).hom
      (SheafOfModules.unit (componentOver X component).left.ringCatSheaf) 1 = 0

namespace RationalTail

/-- Build a rational tail from explicit component and attachment data. -/
noncomputable def ofComponent
    (X : SchemeOverField k) (Z : irreducibleComponents X.left)
    (x : intersection X Z)
    (h_closed : x ∈ closedPoints (intersection X Z))
    (h_nonempty : Nonempty (complementIdeal X Z).subscheme)
    (h_unique : ∀ y : intersection X Z, y = x)
    (h_reduced : IsReduced (intersection X Z))
    (h_eval : Function.Bijective (attachmentEvaluation X Z x))
    (h_genus : Scheme.Hom.cohomologyFinrank (componentOver X Z).hom
      (SheafOfModules.unit (componentOver X Z).left.ringCatSheaf) 1 = 0) :
    RationalTail X :=
  { component := Z
    attachment := x
    attachment_closed := h_closed
    complement_nonempty := h_nonempty
    intersection_unique := h_unique
    intersection_reduced := h_reduced
    evaluation_bijective := h_eval
    genus_zero := h_genus }

/-- The component collapse selected by a rational tail. -/
noncomputable def collapse {X : SchemeOverField k} (T : RationalTail X) :
    (componentIdeal X T.component).subscheme ⟶ (complementIdeal X T.component).subscheme :=
  canonicalCollapse X T.component T.attachment T.evaluation_bijective

/-- The attachment point, viewed as a point of the ambient scheme. -/
noncomputable def attachmentPoint {X : SchemeOverField k}
    (T : RationalTail X) : X.left :=
  (toComponent X T.component ≫ (componentIdeal X T.component).subschemeι) T.attachment

/-- The selected intersection point maps to a closed point of the ambient scheme. -/
theorem attachmentPoint_closed {X : SchemeOverField k} (T : RationalTail X) :
    T.attachmentPoint ∈ closedPoints X.left := sorry

/-- The canonical residue-field comparison from the ambient attachment point to the
intersection residue field. -/
noncomputable def attachmentResidueFieldMap {X : SchemeOverField k}
    (T : RationalTail X) :
    X.left.residueField T.attachmentPoint →+*
      (intersection X T.component).residueField T.attachment :=
  ((toComponent X T.component ≫ (componentIdeal X T.component).subschemeι).residueFieldMap
    T.attachment).hom

/-- The residue-field comparison is an isomorphism at the unique reduced attachment point. -/
theorem attachmentResidueFieldMap_bijective {X : SchemeOverField k}
    (T : RationalTail X) :
    Function.Bijective T.attachmentResidueFieldMap := sorry

/-- The unique reduced attachment intersection satisfies its defining specification. -/
theorem intersection_spec {X : SchemeOverField k} (T : RationalTail X) :
    (∀ y : intersection X T.component, y = T.attachment) ∧
      IsReduced (intersection X T.component) := sorry

/-- The component evaluation and genus-zero conditions satisfy their defining specification. -/
theorem cohomology_spec {X : SchemeOverField k} (T : RationalTail X) :
    Function.Bijective (attachmentEvaluation X T.component T.attachment) ∧
      Scheme.Hom.cohomologyFinrank (componentOver X T.component).hom
        (SheafOfModules.unit (componentOver X T.component).left.ringCatSheaf) 1 = 0 := sorry

/-- A reduced scheme is the scheme-theoretic union of a rational tail and its complement. -/
theorem union_eq_bot {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X) :
    componentIdeal X T.component ⊓ complementIdeal X T.component = ⊥ := sorry

/-- The component collapse agrees with the complementary inclusion on the intersection. -/
theorem collapse_compatibility {X : SchemeOverField k} (T : RationalTail X) :
    toComponent X T.component ≫ T.collapse = toComplement X T.component := sorry

/-- The canonical comparison from the ambient scheme to its scheme-theoretic union. -/
noncomputable def toUnion {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X) :
    X.left ⟶ Scheme.schemeTheoreticUnion (componentIdeal X T.component)
      (complementIdeal X T.component) :=
  (inv ((Scheme.IdealSheafData.subschemeι (⊥ : X.left.IdealSheafData)))) ≫
    eqToHom (congrArg Scheme.IdealSheafData.subscheme T.union_eq_bot).symm

/-- The underlying scheme map of the rational-tail contraction. -/
noncomputable def contractionUnderlying {X : SchemeOverField k}
    [IsReduced X.left] (T : RationalTail X) :
    X.left ⟶ (complementIdeal X T.component).subscheme :=
  T.toUnion ≫
    (schemeTheoreticUnion_isPushout (componentIdeal X T.component)
      (complementIdeal X T.component)).desc T.collapse (𝟙 _) T.collapse_compatibility

/-- The contraction is the unique map with the identity and collapse restrictions. -/
theorem contraction_unique {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X)
    {f : X.left ⟶ (complementIdeal X T.component).subscheme}
    (h_complement : (complementIdeal X T.component).subschemeι ≫ f = 𝟙 _)
    (h_component : (componentIdeal X T.component).subschemeι ≫ f = T.collapse) :
    f = T.contractionUnderlying := sorry

/-- The contraction is a morphism over the base field. -/
theorem contraction_overBase {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X) :
    T.contractionUnderlying ≫ (complementIdeal X T.component).subschemeι ≫ X.hom = X.hom := sorry

/-- The canonical morphism over the base field contracts the selected component onto its
scheme-theoretic complementary closure. -/
noncomputable def contraction {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X) : X ⟶ complementOver X T.component :=
  Over.homMk T.contractionUnderlying T.contraction_overBase

/-- The attachment point is a node under the proper one-dimensional at-worst-nodal hypotheses. -/
theorem attachment_isNode
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    isNode X T.attachmentPoint := sorry

/-- The attachment residue field is finite over the base field. -/
theorem attachmentField_finite
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    FiniteDimensional k (X.left.residueField T.attachmentPoint) := sorry

/-- The attachment residue field is separable over the base field. -/
theorem attachmentField_separable
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    Algebra.IsSeparable k (X.left.residueField T.attachmentPoint) := sorry

/-- The contraction restricts to the identity on the complementary closure. -/
theorem restricts_to_complement {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X) :
    (complementIdeal X T.component).subschemeι ≫ T.contraction.left = 𝟙 _ := sorry

/-- The contraction restricts to the component collapse on the selected component. -/
theorem restricts_to_component {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X) :
    (componentIdeal X T.component).subschemeι ≫ T.contraction.left = T.collapse := sorry

/-- The contraction induces an isomorphism on the structure-sheaf pushforward. -/
theorem pushforward_iso
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [IsReduced X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    IsIso (commRingSheafPushforwardMap T.contraction.left.toShHom) := sorry

/-- The first higher direct image of the structure sheaf under the contraction vanishes. -/
theorem higherDirectImage_one_isZero
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [IsReduced X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    IsZero (higherDirectImageModule T.contraction.left.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf) 1) := sorry

/-- The complementary closure is proper over the base field. -/
theorem complement_proper
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    IsProper (complementOver X T.component).hom := sorry

/-- The complementary closure is one-dimensional. -/
theorem complement_dimension
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    topologicalKrullDim (complementOver X T.component).left = 1 := sorry

/-- The complementary closure has at-worst-nodal singularities. -/
theorem complement_atWorstNodal
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    atWorstNodal (complementOver X T.component) := sorry

/-- The complementary closure has the same global functions as the base field. -/
theorem complement_globalSections
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    Function.Bijective (Scheme.Hom.globalSectionsMap (complementOver X T.component).hom) := sorry

/-- Contraction preserves the cohomological genus. -/
theorem genus_eq
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X) :
    Scheme.Hom.cohomologyFinrank (complementOver X T.component).hom
        (SheafOfModules.unit (complementOver X T.component).left.ringCatSheaf) 1 =
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf) 1 := sorry

/-- The cohomological genus equality agrees with the canonical numerical genus. -/
theorem genus_eq_of_target
    (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X)
    [IsProper (complementOver X T.component).hom]
    (h_target_dimension : topologicalKrullDim (complementOver X T.component).left = 1)
    (h_target_global :
      Function.Bijective (Scheme.Hom.globalSectionsMap (complementOver X T.component).hom)) :
    SchemeOverField.genus (complementOver X T.component) h_target_dimension h_target_global =
      SchemeOverField.genus X h_dimension h_global := sorry

end RationalTail

/-- A reduced irreducible component of a proper scheme over a field is proper over that field. -/
def componentOver_isProper
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (Z : irreducibleComponents X.left) :
    IsProper (RationalTail.componentOver X Z).hom := sorry

/-- Every irreducible component of a proper one-dimensional scheme with constant global
sections is one-dimensional. -/
theorem componentOver_dimension_eq_one
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (Z : irreducibleComponents X.left) :
    topologicalKrullDim (RationalTail.componentOver X Z).left = 1 := sorry

/-- The pullback of the curve dualizing module to a nodal one-dimensional component is
invertible. -/
def dualizingRestriction_isInvertible
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [EquidimensionalSpace X.left] [Fact (topologicalKrullDim X.left = 1)]
    [Fact (atWorstNodal X)] (Z : irreducibleComponents X.left) :
    Scheme.Modules.Invertible
      ((Scheme.Modules.pullback (RationalTail.componentIdeal X Z).subschemeι).obj
        (Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule X.hom)) := sorry

/-- For a proper one-dimensional at-worst-nodal scheme over a field with constant global
sections, the curve dualizing module has negative degree on every rational tail. -/
theorem dualizingRestrictionDegree_lt_zero_of_rationalTail
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) :
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
    ∀ (C : RationalTail X),
      @Scheme.Modules.curveDegreeOfInvertible k _ _
          (RationalTail.componentOver X C.component).hom
          (componentOver_isProper X C.component)
          (componentOver_dimension_eq_one X h_dimension h_global C.component).le
          ((Scheme.Modules.pullback
            (RationalTail.componentIdeal X C.component).subschemeι).obj
            (Scheme.DerivedQCoh.ProperDualizingComplex.curveDualizingModule X.hom))
          (dualizingRestriction_isInvertible X C.component) < 0 := sorry

end AlgebraicGeometry.SchemeOverField
