module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Exactness
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- Inverse image `π_S⁻¹` on abelian sheaves along identity-base étale relocalization. -/
def etalePiInverseImage (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P] :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u} :=
  (relocalizationFunctor (𝟙 S)).sheafPullback AddCommGrpCat.{u}
    S.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- Direct image `π_{S,*}` on abelian sheaves along identity-base étale relocalization. -/
def etalePiPushforward (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}] :
    Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u} ⥤
      Sheaf S.smallEtaleTopology AddCommGrpCat.{u} :=
  (relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- Inverse image `π_S⁻¹` preserves finite limits. -/
instance etalePiInverseImage_preservesFiniteLimits (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))] :
    PreservesFiniteLimits (etalePiInverseImage S) := sorry

/-- Inverse image `π_S⁻¹` preserves finite colimits. -/
instance etalePiInverseImage_preservesFiniteColimits (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))] :
    PreservesFiniteColimits (etalePiInverseImage S) := sorry

/-- Direct image `π_{S,*}` preserves finite limits. -/
instance etalePiPushforward_preservesFiniteLimits (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}] :
    PreservesFiniteLimits (etalePiPushforward S) := sorry

/-- Direct image `π_{S,*}` preserves finite colimits. -/
instance etalePiPushforward_preservesFiniteColimits (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}] :
    PreservesFiniteColimits (etalePiPushforward S) := sorry

/-- Inverse image `π_S⁻¹` is additive. -/
instance etalePiInverseImage_additive (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [Preadditive (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [Preadditive (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P] :
    (etalePiInverseImage S).Additive := sorry

/-- Direct image `π_{S,*}` is additive. -/
instance etalePiPushforward_additive (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [Preadditive (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [Preadditive (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})] :
    (etalePiPushforward S).Additive := sorry

/-- Sheaf-level adjunction `π_S⁻¹ ⊣ π_{S,*}`. -/
def etalePiAdjunction (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P] :
    etalePiInverseImage S ⊣ etalePiPushforward S :=
  (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- Derived adjunction of the exact functors `π_S⁻¹` and `π_{S,*}`. -/
def etalePiDerivedAdjunction (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))] :=
  Adjunction.mapDerivedCategory (etalePiAdjunction S)

/-- The sheaf-level adjunction unit of `π_S⁻¹ ⊣ π_{S,*}` is an isomorphism. -/
theorem etalePiAdjunction_unit_isIso (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((etalePiAdjunction S).unit.app F) := sorry

/-- Sheaf-level composite `π_{S,*} ∘ π_S⁻¹` is the identity functor. -/
def etalePi_comp_inverseImage (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P] :
    etalePiInverseImage S ⋙ etalePiPushforward S ≅
      𝟭 (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun F =>
      have : IsIso ((etalePiAdjunction S).unit.app F) :=
        etalePiAdjunction_unit_isIso S F
      (asIso ((etalePiAdjunction S).unit.app F)).symm)
    (fun {X Y} (f : X ⟶ Y) => sorry)

/-- The unit of the derived small-to-big étale adjunction is an isomorphism. -/
theorem etalePiDerivedAdjunction_unit_isIso (S : Scheme.{u})
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [Abelian (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasDerivedCategory
      (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
    [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).op.lan :
        (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})) :
    IsIso ((etalePiDerivedAdjunction S).unit.app K) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
