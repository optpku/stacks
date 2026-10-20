module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ClosedOpen

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) (P : Compactification.Of Y X)
variable {Z : Scheme.{u}} (i : Z ⟶ X.left) (Λ : Type u) [CommRing Λ]
variable [IsClosedImmersion i]
variable [hsep : IsSeparated X.hom] [hft : Scheme.Hom.FiniteType X.hom]
variable [hY : CompactSpace Y] [hYqs : QuasiSeparatedSpace Y]
variable [hX : CompactSpace X.left] [hXqs : QuasiSeparatedSpace X.left]
variable [hU : CompactSpace (closedImmersionComplement i).toScheme]
variable (Pg : Compactification.Of Y
  (⟨(closedImmersionComplement i).toScheme, ⟨⟨⟩⟩,
    (closedImmersionComplement i).ι ≫ X.hom⟩ : Over Y))
variable (Ph : Compactification.Of Y (⟨Z, ⟨⟨⟩⟩, i ≫ X.hom⟩ : Over Y))
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ F : (closedImmersionComplement i).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (closedImmersionComplement i).ι).op.HasLeftKanExtension F]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback i).op.HasLeftKanExtension G]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify
  (closedImmersionComplement i).toScheme.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory
  (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
    (ModuleCat.{u} Λ))]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : (closedImmersionComplement i).toScheme.Etale,
  HasWeakSheafify
    ((closedImmersionComplement i).toScheme.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [(etaleRestrictionSheaf (closedImmersionComplement i).ι
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (closedImmersionComplement i).ι
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (closedImmersionComplement i).ι (ModuleCat.{u} Λ))]
variable [((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology).Additive]
variable [PreservesFiniteLimits
  ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback i).sheafPushforwardContinuous (ModuleCat.{u} Λ)
    X.left.smallEtaleTopology Z.smallEtaleTopology)]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

variable [HasSheafify Pg.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Pg.obj.right.left.Etale,
  HasWeakSheafify (Pg.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Pg.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : (closedImmersionComplement i).toScheme.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι Pg)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι Pg)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι Pg) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι Pg) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback Pg.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    Pg.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback Pg.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      Pg.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Pg.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [HasSheafify Ph.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Ph.obj.right.left.Etale,
  HasWeakSheafify (Ph.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Ph.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι Ph)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι Ph)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι Ph) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι Ph) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback Ph.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    Ph.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback Ph.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      Ph.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Ph.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

include hsep hft hY hYqs hX hXqs hU

namespace etaleDerivedLowerShriek

/-- For a separated finite-type morphism of quasi-compact quasi-separated schemes,
a quasi-compact complementary open gives a distinguished triangle on the actual
restricted derived lower-shriek values of an admissible complex. The first two
maps are the transported images of the complementary adjunction counit and unit.
Admissibility means torsion coefficients or bounded-below torsion cohomology. -/
theorem closedOpen_distinguished
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : AddMonoid.IsTorsion Λ ∨
      (etaleDerivedIsTorsion K ∧ ∃ n, DerivedCategory.IsGE K n)) :
    let F := etaleDerivedLowerShriek (Λ := Λ) X P
    let G := etaleDerivedLowerShriek (Λ := Λ)
      (⟨(closedImmersionComplement i).toScheme, ⟨⟨⟩⟩,
        (closedImmersionComplement i).ι ≫ X.hom⟩ : Over Y) Pg
    let H := etaleDerivedLowerShriek (Λ := Λ) (⟨Z, ⟨⟨⟩⟩, i ≫ X.hom⟩ : Over Y) Ph
    let KU := (etaleDerivedRestriction (closedImmersionComplement i).ι Λ).obj K
    let KZ := ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
      X.left.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory.obj K
    ∃ (eU : F.obj ((etaleDerivedExtensionByZeroRestrict
          (closedImmersionComplement i).ι Λ).obj K) ≅ G.obj KU)
      (eZ : F.obj ((etaleDerivedClosedOpenClosed i Λ).obj K) ≅ H.obj KZ)
      (δ : H.obj KZ ⟶ (G.obj KU)⟦(1 : ℤ)⟧),
      Triangle.mk
        (eU.inv ≫ F.map ((etaleDerivedClosedOpenCounit i Λ).app K))
        (F.map ((etaleDerivedClosedOpenUnit i Λ).app K) ≫ eZ.hom) δ ∈
          distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := by
  sorry

/-- Over a torsion coefficient ring, the complementary distinguished triangle
of derived lower shriek exists for every complex, with the transported canonical
counit and unit as its first two maps. -/
theorem closedOpen_distinguished_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    let F := etaleDerivedLowerShriek (Λ := Λ) X P
    let G := etaleDerivedLowerShriek (Λ := Λ)
      (⟨(closedImmersionComplement i).toScheme, ⟨⟨⟩⟩,
        (closedImmersionComplement i).ι ≫ X.hom⟩ : Over Y) Pg
    let H := etaleDerivedLowerShriek (Λ := Λ) (⟨Z, ⟨⟨⟩⟩, i ≫ X.hom⟩ : Over Y) Ph
    let KU := (etaleDerivedRestriction (closedImmersionComplement i).ι Λ).obj K
    let KZ := ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
      X.left.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory.obj K
    ∃ (eU : F.obj ((etaleDerivedExtensionByZeroRestrict
          (closedImmersionComplement i).ι Λ).obj K) ≅ G.obj KU)
      (eZ : F.obj ((etaleDerivedClosedOpenClosed i Λ).obj K) ≅ H.obj KZ)
      (δ : H.obj KZ ⟶ (G.obj KU)⟦(1 : ℤ)⟧),
      Triangle.mk
        (eU.inv ≫ F.map ((etaleDerivedClosedOpenCounit i Λ).app K))
        (F.map ((etaleDerivedClosedOpenUnit i Λ).app K) ≫ eZ.hom) δ ∈
          distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := by
  exact closedOpen_distinguished X P i Λ Pg Ph K (Or.inl hΛ)

/-- A bounded-below complex with torsion cohomology has a complementary
distinguished triangle of derived lower shriek whose first two maps are the
transported canonical counit and unit. -/
theorem closedOpen_distinguished_of_isGE_isTorsion
    {n : ℤ} (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K)
    [DerivedCategory.IsGE K n] :
    let F := etaleDerivedLowerShriek (Λ := Λ) X P
    let G := etaleDerivedLowerShriek (Λ := Λ)
      (⟨(closedImmersionComplement i).toScheme, ⟨⟨⟩⟩,
        (closedImmersionComplement i).ι ≫ X.hom⟩ : Over Y) Pg
    let H := etaleDerivedLowerShriek (Λ := Λ) (⟨Z, ⟨⟨⟩⟩, i ≫ X.hom⟩ : Over Y) Ph
    let KU := (etaleDerivedRestriction (closedImmersionComplement i).ι Λ).obj K
    let KZ := ((smallEtalePullback i).sheafPullback (ModuleCat.{u} Λ)
      X.left.smallEtaleTopology Z.smallEtaleTopology).mapDerivedCategory.obj K
    ∃ (eU : F.obj ((etaleDerivedExtensionByZeroRestrict
          (closedImmersionComplement i).ι Λ).obj K) ≅ G.obj KU)
      (eZ : F.obj ((etaleDerivedClosedOpenClosed i Λ).obj K) ≅ H.obj KZ)
      (δ : H.obj KZ ⟶ (G.obj KU)⟦(1 : ℤ)⟧),
      Triangle.mk
        (eU.inv ≫ F.map ((etaleDerivedClosedOpenCounit i Λ).app K))
        (F.map ((etaleDerivedClosedOpenUnit i Λ).app K) ≫ eZ.hom) δ ∈
          distTriang (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := by
  exact closedOpen_distinguished X P i Λ Pg Ph K
    (Or.inr ⟨h_tors, n, inferInstance⟩)

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
