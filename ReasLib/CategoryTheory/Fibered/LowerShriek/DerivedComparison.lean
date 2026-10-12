/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LowerShriek.Derived
public import ReasLib.CategoryTheory.Sites.Topos.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison maps for derived lower shriek

This file owns the projection lower-shriek functor, its compatibility with composition, and the
canonical map induced by a morphism into an underived inverse image.  In particular, downstream
users do not supply either the projection-composition isomorphism or the degree-zero comparison.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FiberedCategoryOver.DerivedLowerShriek

variable {D : RingedSite.{u, v}}
variable {C C' : FiberedCategoryOver.{u, v, u, v} D.carrier}

/-- Abelian sheaves on the inherited site of a fibered category. -/
@[stacks 08PD "abelian sheaves on an inherited site"]
abbrev AbSheaf (D : RingedSite.{u, v})
    (C : FiberedCategoryOver.{u, v, u, v} D.carrier) :=
  Sheaf (sourceTopology D C) AddCommGrpCat.{max u v}

/-- Abelian sheaves on the base site. -/
@[stacks 08PD "abelian sheaves on the base site"]
abbrev BaseAbSheaf (D : RingedSite.{u, v}) :=
  Sheaf D.siteTopology AddCommGrpCat.{max u v}

/-- The derived category of abelian sheaves on an inherited site. -/
@[stacks 08PD "derived abelian sheaves on an inherited site"]
abbrev DerivedAbSheaf (D : RingedSite.{u, v})
    (C : FiberedCategoryOver.{u, v, u, v} D.carrier) :=
  DerivedCategory (AbSheaf D C)

/-- The derived category of abelian sheaves on the base site. -/
@[stacks 08PD "derived abelian sheaves on the base site"]
abbrev DerivedBaseAbSheaf (D : RingedSite.{u, v}) :=
  DerivedCategory (BaseAbSheaf D)

/-- The exact inverse image along the projection of a fibered category to its base site. -/
@[stacks 08PD "exact inverse image along a fibered projection"]
noncomputable abbrev projectionInverseImageExact
    (D : RingedSite.{u, v}) (C : FiberedCategoryOver.{u, v, u, v} D.carrier)
    [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
    [HasSheafify D.siteTopology AddCommGrpCat.{max u v}] :
    BaseAbSheaf D ⥤ₑ AbSheaf D C :=
  siteAbelianInverseImageExact (sourceTopology D C) D.siteTopology C.p

/-- The derived inverse image along the projection of a fibered category to its base site. -/
@[stacks 08PD "derived inverse image along a fibered projection"]
noncomputable abbrev projectionInverseImage
    (D : RingedSite.{u, v}) (C : FiberedCategoryOver.{u, v, u, v} D.carrier)
    [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
    [HasSheafify D.siteTopology AddCommGrpCat.{max u v}]
    [UnivLE.{max u v, max u v}] :
    DerivedBaseAbSheaf D ⥤ DerivedAbSheaf D C :=
  (projectionInverseImageExact D C).mapDerivedCategory

namespace projectionInverseImage

/-- Derived inverse image along a fibered projection admits a left adjoint. -/
@[stacks 08PD "projection derived lower-shriek existence", instance]
theorem isRightAdjoint
    (D : RingedSite.{u, v}) (C : FiberedCategoryOver.{u, v, u, v} D.carrier)
    [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
    [HasSheafify D.siteTopology AddCommGrpCat.{max u v}]
    [UnivLE.{max u v, max u v}] :
    Functor.IsRightAdjoint (projectionInverseImage D C) := sorry

end projectionInverseImage

/-- The derived lower-shriek functor along a fibered projection. -/
@[stacks 08PD "projection derived lower shriek"]
noncomputable abbrev projectionLowerShriek
    (D : RingedSite.{u, v}) (C : FiberedCategoryOver.{u, v, u, v} D.carrier)
    [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
    [HasSheafify D.siteTopology AddCommGrpCat.{max u v}]
    [UnivLE.{max u v, max u v}] :
    DerivedAbSheaf D C ⥤ DerivedBaseAbSheaf D :=
  Functor.leftAdjoint (projectionInverseImage D C)

/-- The adjunction characterizing derived lower shriek along a fibered projection. -/
@[stacks 08PD "projection derived lower-shriek adjunction"]
noncomputable def projectionAdjunction
    (D : RingedSite.{u, v}) (C : FiberedCategoryOver.{u, v, u, v} D.carrier)
    [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
    [HasSheafify D.siteTopology AddCommGrpCat.{max u v}]
    [UnivLE.{max u v, max u v}] :
    projectionLowerShriek D C ⊣ projectionInverseImage D C :=
  Adjunction.ofIsRightAdjoint (projectionInverseImage D C)

section Composition

variable (f : C' ⟶ C)
variable [IsMorphismOfSites
  (sourceTopology D C') (sourceTopology D C) (FiberedCategoryOver.toFunctor f)]
variable [Functor.IsCocontinuous
  (FiberedCategoryOver.toFunctor f) (sourceTopology D C') (sourceTopology D C)]
variable [HasSheafify (sourceTopology D C') AddCommGrpCat.{max u v}]
variable [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
variable [HasSheafify D.siteTopology AddCommGrpCat.{max u v}]
variable [UnivLE.{max u v, max u v}]

/-- The exact inverse image along the projection of `C'` agrees with first pulling back along the
projection of `C` and then along `f`. -/
@[stacks 08PD "exact projection inverse-image composition"]
noncomputable def projectionInverseImageExactCompIso :
    (projectionInverseImageExact D C).comp (abelianInverseImageExact f) ≅
      projectionInverseImageExact D C' :=
  ObjectProperty.isoMk _
    (Functor.sheafPushforwardContinuousComp'
      (F := FiberedCategoryOver.toFunctor f) (G := C.p) (FG := C'.p)
      (eFG := eqToIso (FiberedCategoryOver.comm f))
      AddCommGrpCat.{max u v} (sourceTopology D C')
      (sourceTopology D C) D.siteTopology)

/-- Derived inverse image along the projection of `C'` agrees with the composite of the two
derived inverse images. -/
@[stacks 08PD "derived projection inverse-image composition"]
noncomputable def projectionInverseImageCompIso :
    projectionInverseImage D C ⋙ abelianInverseImage f ≅
      projectionInverseImage D C' :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (projectionInverseImageExact D C) (abelianInverseImageExact f)).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      (projectionInverseImageExactCompIso f)

/-- The projection derived lower shriek from `C'` agrees with lower shriek along `f` followed by
projection derived lower shriek from `C`. -/
@[stacks 08PD "projection derived lower-shriek composition"]
noncomputable def projectionLowerShriekCompIso :
    projectionLowerShriek D C' ≅
      abelianLowerShriek f ⋙ projectionLowerShriek D C :=
  (projectionAdjunction D C').leftAdjointUniq
    (((abelianAdjunction f).comp (projectionAdjunction D C)).ofNatIsoRight
      (projectionInverseImageCompIso f))

end Composition

/-- The degree-zero embedding for abelian sheaves on an inherited site. -/
@[stacks 08PD "degree-zero embedding on an inherited site"]
abbrev single (D : RingedSite.{u, v})
    (C : FiberedCategoryOver.{u, v, u, v} D.carrier) :
    AbSheaf D C ⥤ DerivedAbSheaf D C :=
  DerivedCategory.singleFunctor (AbSheaf D C) (0 : ℤ)

section Comparison

variable (f : C' ⟶ C)
variable [IsMorphismOfSites
  (sourceTopology D C') (sourceTopology D C) (FiberedCategoryOver.toFunctor f)]
variable [Functor.IsCocontinuous
  (FiberedCategoryOver.toFunctor f) (sourceTopology D C') (sourceTopology D C)]
variable [HasSheafify (sourceTopology D C') AddCommGrpCat.{max u v}]
variable [HasSheafify (sourceTopology D C) AddCommGrpCat.{max u v}]
variable [HasSheafify D.siteTopology AddCommGrpCat.{max u v}]
variable [UnivLE.{max u v, max u v}]

/-- A morphism into the underived inverse image induces its canonical degree-zero morphism into
the exact derived inverse image. -/
@[stacks 08PD "degree-zero inverse-image comparison"]
noncomputable def singleToInverseImage
    {F : AbSheaf D C} {F' : AbSheaf D C'}
    (t : F' ⟶ (FiberedCategoryOver.abelianInverseImage f).obj F) :
    (single D C').obj F' ⟶ (abelianInverseImage f).obj ((single D C).obj F) :=
  (single D C').map t ≫
    ((FiberedCategoryOver.abelianInverseImage f).mapDerivedCategorySingleFunctor 0).inv.app F

/-- The adjoint transpose of `singleToInverseImage`; this is the canonical degree-zero map from
derived lower shriek along `f` to the target sheaf in degree zero. -/
@[stacks 08PD "degree-zero derived lower-shriek comparison"]
noncomputable def lowerShriekSingleComparison
    {F : AbSheaf D C} {F' : AbSheaf D C'}
    (t : F' ⟶ (FiberedCategoryOver.abelianInverseImage f).obj F) :
    (abelianLowerShriek f).obj ((single D C').obj F') ⟶ (single D C).obj F :=
  ((abelianAdjunction f).homEquiv _ _).symm (singleToInverseImage f t)

/-- Remark 21.38.7 (08PD): the canonical map
`Lπ'_!.obj (single.obj F') ⟶ Lπ_!.obj (single.obj F)` induced by
`t : F' ⟶ g⁻¹.obj F`. -/
@[stacks 08PD]
noncomputable def comparisonMap
    {F : AbSheaf D C} {F' : AbSheaf D C'}
    (t : F' ⟶ (FiberedCategoryOver.abelianInverseImage f).obj F) :
    (projectionLowerShriek D C').obj ((single D C').obj F') ⟶
      (projectionLowerShriek D C).obj ((single D C).obj F) :=
  (projectionLowerShriekCompIso f).hom.app ((single D C').obj F') ≫
    (projectionLowerShriek D C).map (lowerShriekSingleComparison f t)

end Comparison

-- All displayed maps and isomorphisms above are built from exact-derived functoriality,
-- composition of continuous inverse images, and uniqueness of adjoints.  Deferred axioms enter
-- only through the Prop-valued exactness, continuity, and adjoint-existence certificates.

end CategoryTheory.FiberedCategoryOver.DerivedLowerShriek
