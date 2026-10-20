module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Composition.Plus
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Naturality
public import ReasLib.CategoryTheory.Functor.Exactness.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.BoundedBelow

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.IsBlowup.Etale

variable {X X' : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (p : A ⟶ B),
    (abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C),
    (abelianPushforwardAlong f ⋙ abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]

/-- The composite of the exceptional projection with the center immersion. -/
def composite (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    (I.comap b).subscheme ⟶ X :=
  exceptionalProjection I b ≫ I.subschemeι

/-- The bundled exact functors of iterated and composite small-étale inverse images. -/
noncomputable def pullbackExactCompIso {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    (etalePullbackExact p).comp (etalePullbackExact q) ≅ etalePullbackExact (q ≫ p) :=
  (CategoryTheory.exactFunctor
      (Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf C.smallEtaleTopology AddCommGrpCat.{u})).isoMk
    (etaleAbelianSheafPullback_comp p q)

/-- `pullbackExactCompIso` is the bundled form of `etaleAbelianSheafPullback_comp`. -/
theorem pullbackExactCompIso_eq {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    pullbackExactCompIso p q =
      (CategoryTheory.exactFunctor
          (Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
          (Sheaf C.smallEtaleTopology AddCommGrpCat.{u})).isoMk
        (etaleAbelianSheafPullback_comp p q) := sorry

/-- Derived inverse image along a composite morphism is the iterated inverse image. -/
noncomputable def inverseImageCompIso {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    etaleDerivedInverseImage p ⋙ etaleDerivedInverseImage q ≅
      etaleDerivedInverseImage (q ≫ p) :=
  (ExactFunctor.Derived.Plus.compFunctorIso (etalePullbackExact p) (etalePullbackExact q)).symm ≪≫
    ExactFunctor.Derived.Plus.mapIso (pullbackExactCompIso p q)

/-- `inverseImageCompIso` is the exact-functor composition comparison followed by the
underived pullback identification. -/
theorem inverseImageCompIso_eq {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    inverseImageCompIso p q =
      (ExactFunctor.Derived.Plus.compFunctorIso
          (etalePullbackExact p) (etalePullbackExact q)).symm ≪≫
        ExactFunctor.Derived.Plus.mapIso (pullbackExactCompIso p q) := sorry

/-- Direct image of abelian small-étale sheaves along a composite is the iterated direct image. -/
noncomputable def abelianPushforwardAlong_comp {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) :
    abelianPushforwardAlong q ⋙ abelianPushforwardAlong p ≅
      abelianPushforwardAlong (q ≫ p) :=
  conjugateIsoEquiv
    (((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
        A.smallEtaleTopology B.smallEtaleTopology).comp
      ((smallEtalePullback q).sheafAdjunctionContinuous AddCommGrpCat.{u}
        B.smallEtaleTopology C.smallEtaleTopology))
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology C.smallEtaleTopology)
    (etaleAbelianSheafPullback_comp p q).symm

/-- `abelianPushforwardAlong_comp` is the mate of the inverse-image composition isomorphism. -/
theorem abelianPushforwardAlong_comp_eq {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    abelianPushforwardAlong_comp p q =
      conjugateIsoEquiv
        (((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
            A.smallEtaleTopology B.smallEtaleTopology).comp
          ((smallEtalePullback q).sheafAdjunctionContinuous AddCommGrpCat.{u}
            B.smallEtaleTopology C.smallEtaleTopology))
        ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous AddCommGrpCat.{u}
          A.smallEtaleTopology C.smallEtaleTopology)
        (etaleAbelianSheafPullback_comp p q).symm := sorry

/-- Canonical comparison `R(g ∘ f)_* ⟶ Rf_* ⋙ Rg_*` on `D⁺` of abelian small-étale sheaves. -/
noncomputable def pushforwardCompComparison {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    etaleDerivedPushforward (f ≫ g) ⟶
      etaleDerivedPushforward f ⋙ etaleDerivedPushforward g :=
  (sourceIsoOfIso (abelianPushforwardAlong f) (abelianPushforwardAlong g)
      (abelianPushforwardAlong_comp g f).symm).hom ≫
    comparison (abelianPushforwardAlong f) (abelianPushforwardAlong g)

/-- `pushforwardCompComparison` is the source identification of `R(g ∘ f)_*` with
`R(f_* ⋙ g_*)`, followed by the standard composition comparison. -/
theorem pushforwardCompComparison_eq {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    pushforwardCompComparison f g =
      (sourceIsoOfIso (abelianPushforwardAlong f) (abelianPushforwardAlong g)
          (abelianPushforwardAlong_comp g f).symm).hom ≫
        comparison (abelianPushforwardAlong f) (abelianPushforwardAlong g) := sorry

/-- Derived pushforward along a composite of scheme morphisms is isomorphic to the
composition of derived pushforwards on `D⁺` of abelian small-étale sheaves. -/
instance pushforwardCompComparison_isIso {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    IsIso (pushforwardCompComparison f g) := sorry

/-- The unit of the bounded-below derived adjunction `p⁻¹ ⊣ Rp_*` at `K`. -/
noncomputable def unitApp {A B : Scheme.{u}} (p : A ⟶ B)
    (K : DerivedCategory.Plus (Sheaf B.smallEtaleTopology AddCommGrpCat.{u})) :
    K ⟶ (etaleDerivedPushforward p).obj ((etaleDerivedInverseImage p).obj K) :=
  (Adjunction.Derived.Plus.adjunction (etalePullbackExact p) (abelianPushforwardAlong p)
      ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
        B.smallEtaleTopology A.smallEtaleTopology)).unit.app K

/-- `unitApp` is the component of the bounded-below derived adjunction unit. -/
theorem unitApp_eq {A B : Scheme.{u}} (p : A ⟶ B)
    (K : DerivedCategory.Plus (Sheaf B.smallEtaleTopology AddCommGrpCat.{u})) :
    unitApp p K =
      (Adjunction.Derived.Plus.adjunction (etalePullbackExact p) (abelianPushforwardAlong p)
          ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
            B.smallEtaleTopology A.smallEtaleTopology)).unit.app K := sorry

/-- The canonical comparison from `K` to the derived pushforward along the center. -/
noncomputable def toCenter (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus.ι.obj K ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward I.subschemeι).obj
          ((etaleDerivedInverseImage I.subschemeι).obj K)) :=
  DerivedCategory.Plus.ι.map (unitApp I.subschemeι K)

/-- `toCenter` is the image under `Plus.ι` of the derived adjunction unit along the center. -/
theorem toCenter_def (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    toCenter I b K = DerivedCategory.Plus.ι.map (unitApp I.subschemeι K) := sorry

/-- The canonical comparison from `K` to the derived pushforward along the blow-up. -/
noncomputable def toBlowup (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus.ι.obj K ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward b).obj ((etaleDerivedInverseImage b).obj K)) :=
  DerivedCategory.Plus.ι.map (unitApp b K)

/-- `toBlowup` is the image under `Plus.ι` of the derived adjunction unit along the blow-up. -/
theorem toBlowup_def (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    toBlowup I b K = DerivedCategory.Plus.ι.map (unitApp b K) := sorry

/-- Identification of derived pushforward along the two composites around the blow-up square. -/
noncomputable def composite_pushforwardIso (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    etaleDerivedPushforward ((I.comap b).subschemeι ≫ b) ≅
      etaleDerivedPushforward (composite I b) :=
  eqToIso (congrArg (fun p : (I.comap b).subscheme ⟶ X ↦ etaleDerivedPushforward p)
    ((Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap b) I b
        (I.le_map_comap b)).symm :
      (I.comap b).subschemeι ≫ b = composite I b))

/-- Identification of derived inverse image along the two composites around the blow-up square. -/
noncomputable def composite_inverseImageIso (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    etaleDerivedInverseImage ((I.comap b).subschemeι ≫ b) ≅
      etaleDerivedInverseImage (composite I b) :=
  eqToIso (congrArg (fun p : (I.comap b).subscheme ⟶ X ↦ etaleDerivedInverseImage p)
    ((Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap b) I b
        (I.le_map_comap b)).symm :
      (I.comap b).subschemeι ≫ b = composite I b))

/-- `composite_pushforwardIso` is transport of derived pushforward along the two composites. -/
theorem composite_pushforwardIso_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    composite_pushforwardIso I b =
      eqToIso (congrArg (fun p : (I.comap b).subscheme ⟶ X ↦ etaleDerivedPushforward p)
        ((Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap b) I b
            (I.le_map_comap b)).symm :
          (I.comap b).subschemeι ≫ b = composite I b)) := sorry

/-- `composite_inverseImageIso` is transport of derived inverse image along the two composites. -/
theorem composite_inverseImageIso_eq (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] :
    composite_inverseImageIso I b =
      eqToIso (congrArg (fun p : (I.comap b).subscheme ⟶ X ↦ etaleDerivedInverseImage p)
        ((Scheme.IdealSheafData.subschemeMap_subschemeι (I.comap b) I b
            (I.le_map_comap b)).symm :
          (I.comap b).subschemeι ≫ b = composite I b)) := sorry

/-- The comparison from the center term to the exceptional term of the blow-up square. -/
noncomputable def centerToExceptional (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward I.subschemeι).obj
          ((etaleDerivedInverseImage I.subschemeι).obj K)) ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward (composite I b)).obj
          ((etaleDerivedInverseImage (composite I b)).obj K)) :=
  DerivedCategory.Plus.ι.map
    ((etaleDerivedPushforward I.subschemeι).map
        (unitApp (exceptionalProjection I b)
          ((etaleDerivedInverseImage I.subschemeι).obj K)) ≫
      (asIso (pushforwardCompComparison (exceptionalProjection I b) I.subschemeι)).inv.app
        ((etaleDerivedInverseImage (exceptionalProjection I b)).obj
          ((etaleDerivedInverseImage I.subschemeι).obj K)) ≫
      (etaleDerivedPushforward (composite I b)).map
        ((inverseImageCompIso I.subschemeι (exceptionalProjection I b)).hom.app K))

/-- `centerToExceptional` is derived pushforward of the exceptional-projection unit, followed by
the inverse composition comparison and the inverse-image identification. -/
theorem centerToExceptional_def (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    centerToExceptional I b K =
      DerivedCategory.Plus.ι.map
        ((etaleDerivedPushforward I.subschemeι).map
            (unitApp (exceptionalProjection I b)
              ((etaleDerivedInverseImage I.subschemeι).obj K)) ≫
          (asIso (pushforwardCompComparison (exceptionalProjection I b) I.subschemeι)).inv.app
            ((etaleDerivedInverseImage (exceptionalProjection I b)).obj
              ((etaleDerivedInverseImage I.subschemeι).obj K)) ≫
          (etaleDerivedPushforward (composite I b)).map
            ((inverseImageCompIso I.subschemeι (exceptionalProjection I b)).hom.app K)) :=
  sorry

/-- The comparison from the blow-up term to the exceptional term of the blow-up square. -/
noncomputable def blowupToExceptional (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward b).obj ((etaleDerivedInverseImage b).obj K)) ⟶
      DerivedCategory.Plus.ι.obj
        ((etaleDerivedPushforward (composite I b)).obj
          ((etaleDerivedInverseImage (composite I b)).obj K)) :=
  DerivedCategory.Plus.ι.map
    ((etaleDerivedPushforward b).map
        (unitApp (I.comap b).subschemeι ((etaleDerivedInverseImage b).obj K)) ≫
      (asIso (pushforwardCompComparison (I.comap b).subschemeι b)).inv.app
        ((etaleDerivedInverseImage (I.comap b).subschemeι).obj
          ((etaleDerivedInverseImage b).obj K)) ≫
      (etaleDerivedPushforward ((I.comap b).subschemeι ≫ b)).map
        ((inverseImageCompIso b (I.comap b).subschemeι).hom.app K) ≫
      (composite_pushforwardIso I b).hom.app
        ((etaleDerivedInverseImage ((I.comap b).subschemeι ≫ b)).obj K) ≫
      (etaleDerivedPushforward (composite I b)).map
        ((composite_inverseImageIso I b).hom.app K))

/-- `blowupToExceptional` is derived pushforward of the exceptional-immersion unit, followed by
the inverse composition comparison and transport along the two composites. -/
theorem blowupToExceptional_def (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    blowupToExceptional I b K =
      DerivedCategory.Plus.ι.map
        ((etaleDerivedPushforward b).map
            (unitApp (I.comap b).subschemeι ((etaleDerivedInverseImage b).obj K)) ≫
          (asIso (pushforwardCompComparison (I.comap b).subschemeι b)).inv.app
            ((etaleDerivedInverseImage (I.comap b).subschemeι).obj
              ((etaleDerivedInverseImage b).obj K)) ≫
          (etaleDerivedPushforward ((I.comap b).subschemeι ≫ b)).map
            ((inverseImageCompIso b (I.comap b).subschemeι).hom.app K) ≫
          (composite_pushforwardIso I b).hom.app
            ((etaleDerivedInverseImage ((I.comap b).subschemeι ≫ b)).obj K) ≫
          (etaleDerivedPushforward (composite I b)).map
            ((composite_inverseImageIso I b).hom.app K)) := sorry

/-- The four canonical étale derived comparisons of a blow-up square commute. -/
theorem square (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    CommSq (toCenter I b K) (toBlowup I b K)
      (centerToExceptional I b K) (blowupToExceptional I b K) := sorry

end AlgebraicGeometry.IsBlowup.Etale

end

end
