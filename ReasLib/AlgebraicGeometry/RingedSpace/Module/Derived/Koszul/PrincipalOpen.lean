/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.Algebra.Homology.Koszul.PowerTower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Exact
public import ReasLib.AlgebraicGeometry.Scheme.PrincipalOpen.Cech.Product
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Powered Koszul comparisons on principal opens

This module constructs the canonical maps from sheafified powered Koszul ideal complexes to the
affine structure sheaf and the induced colimit comparison with degree-zero hypercohomology on a
finite union of principal opens.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open KoszulComplex.PowerTower

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

variable {X : RingedSpace.{u}}

/-- The exact derived affine sheafification functor from `D(A)` to
`D(𝒪_{Spec(A)})`. -/
noncomputable abbrev affineDerivedTilde (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u, u} A) ⥤
      ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace :=
  CategoryTheory.ExactFunctor.mapDerivedCategory
    (⟨tilde.functor (CommRingCat.of A), tilde.exact (CommRingCat.of A)⟩ :
      ModuleCat.{u, u} A ⥤ₑ (Spec (CommRingCat.of A)).Modules)

/-- The structure sheaf of `Spec(A)`, placed in degree zero in its derived category. -/
noncomputable abbrev affineUnitDerived (A : Type u) [CommRing A] :
    ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace :=
  (affineDerivedTilde A).obj (DerivedCategory.Q.obj unitSource)

/-- The inverse degree-zero identification used to map the last differential of a
powered Koszul cochain complex to the affine unit complex. -/
noncomputable def unitComponentZeroInv
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    (cochainStage f n).X 0 ⟶ unitSource.X 0 :=
  ((KoszulComplex.powerComplex f n).extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).hom ≫
    (ModuleCat.exteriorPower.iso₀ (ModuleCat.of A (Fin r → A))).hom ≫
    (((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A)).extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl).inv

/-- The degree-zero component of the canonical map from the powered Koszul ideal
complex to the affine unit complex. -/
noncomputable def idealStageZeroToUnit
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    (idealStage f n).X 0 ⟶ unitSource.X 0 :=
  (CochainComplex.shiftFunctorObjXIso
      ((cochainStage f n).stupidTrunc (ComplexShape.embeddingUpIntLE (-1)))
        (-1) 0 (-1) rfl).hom ≫
    ((cochainStage f n).stupidTruncXIso
      (ComplexShape.embeddingUpIntLE (-1)) (i := 0) rfl).hom ≫
    (cochainStage f n).d (-1) 0 ≫ unitComponentZeroInv f n

/-- The componentwise canonical map from the powered Koszul ideal complex to the
affine unit complex. -/
noncomputable def idealStageToUnitComponent
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) (p : ℤ) :
    (idealStage f n).X p ⟶ unitSource.X p :=
  if hp : p = 0 then hp ▸ idealStageZeroToUnit f n else 0

/-- The components of `idealStageToUnitComponent` commute with the differentials. -/
theorem idealStageToUnitComponent_comm
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    idealStageToUnitComponent f n p ≫ unitSource.d p q =
      (idealStage f n).d p q ≫ idealStageToUnitComponent f n q := sorry

/-- The canonical cochain map from a powered Koszul ideal stage to the affine unit
complex. -/
noncomputable def idealStageToUnit
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    idealStage f n ⟶ unitSource :=
  HomologicalComplex.Hom.mk (idealStageToUnitComponent f n)
    (idealStageToUnitComponent_comm f n)

/-- The canonical powered-ideal map is the final differential in degree zero. -/
theorem idealStageToUnit_f_zero
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    (idealStageToUnit f n).f 0 = idealStageZeroToUnit f n := sorry

/-- The canonical powered-ideal map vanishes away from degree zero. -/
theorem idealStageToUnit_f_of_ne_zero
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ)
    (p : ℤ) (hp : p ≠ 0) :
    (idealStageToUnit f n).f p = 0 := sorry

/-- The canonical map from a sheafified powered Koszul ideal stage to the structure
sheaf. -/
noncomputable def poweredIdealToUnit {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (n : ℕ) :
    (derivedIdealSystem f ⋙ affineDerivedTilde A).obj (Opposite.op n) ⟶
      affineUnitDerived A :=
  (affineDerivedTilde A).map (DerivedCategory.Q.map (idealStageToUnit f n))

/-- The canonical powered-ideal maps commute with adjacent transition maps. -/
theorem poweredIdealToUnit_naturality
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    (affineDerivedTilde A).map (derivedIdealStep f n) ≫ poweredIdealToUnit f n =
      poweredIdealToUnit f (n + 1) := sorry

/-- The restriction-Hom presentation of degree-zero cohomology on the principal-open
union. -/
abbrev restrictionHomH0 {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of
    ((moduleRestrictionToOpenDerived (Spec (CommRingCat.of A)).toRingedSpace
        (Scheme.PrincipalOpenCech.openSubset f)).obj (affineUnitDerived A) ⟶
      (moduleRestrictionToOpenDerived (Spec (CommRingCat.of A)).toRingedSpace
        (Scheme.PrincipalOpenCech.openSubset f)).obj E)

/-- The canonical restriction-Hom model of `H⁰(U, E)` is isomorphic to degree-zero
hypercohomology on `Scheme.PrincipalOpenCech.openSubset f`. -/
theorem restrictionHomH0_isomorphic_openH0
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace) :
    IsIsomorphic (restrictionHomH0 f E)
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (moduleOpenHypercohomology (Spec (CommRingCat.of A)).toRingedSpace
          (Scheme.PrincipalOpenCech.openSubset f) E 0)) := sorry

/-- On the union of the principal opens, the canonical powered-ideal map to the
structure sheaf is invertible. -/
noncomputable instance poweredIdealToUnit_restrict_isIso
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    IsIso
      ((moduleRestrictionToOpenDerived (Spec (CommRingCat.of A)).toRingedSpace
        (Scheme.PrincipalOpenCech.openSubset f)).map (poweredIdealToUnit f n)) := sorry

/-- Restriction to the principal-open union sends a morphism out of the `n`th powered
ideal stage to its canonical class in `H⁰(U, E)`. -/
noncomputable def poweredIdealStageComparison
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace) (n : ℕ) :
    AddCommGrpCat.of
        (((derivedIdealSystem f ⋙ affineDerivedTilde A).obj (Opposite.op n)) ⟶ E) ⟶
      restrictionHomH0 f E :=
  AddCommGrpCat.ofHom
      ((moduleRestrictionToOpenDerived (Spec (CommRingCat.of A)).toRingedSpace
        (Scheme.PrincipalOpenCech.openSubset f)).mapAddHom) ≫
    AddCommGrpCat.ofHom
      (Preadditive.leftComp _
        (inv ((moduleRestrictionToOpenDerived (Spec (CommRingCat.of A)).toRingedSpace
          (Scheme.PrincipalOpenCech.openSubset f)).map (poweredIdealToUnit f n))))

/-- The direct system of additive groups `Hom(Iₑ, E)` associated to an inverse
system `I`. -/
abbrev homDiagram (I : SequentialInverseSystem (ModuleDerived X)) (E : ModuleDerived X) :
    (ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  I.op ⋙ preadditiveYoneda.obj E

/-- The canonical stage maps are compatible with the powered Koszul transition maps. -/
theorem poweredIdealStageComparison_naturality
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    {e e' : (ℕᵒᵖ)ᵒᵖ} (g : e ⟶ e') :
    (homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E).map g ≫
        poweredIdealStageComparison f E e'.unop.unop =
      poweredIdealStageComparison f E e.unop.unop ≫
        ((Functor.const _).obj (restrictionHomH0 f E)).map g := sorry

/-- The canonical cocone of stagewise restriction maps from the powered Koszul ideal
system to `H⁰(U, E)`. -/
noncomputable def poweredIdealComparison
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace) :
    homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E ⟶
      (Functor.const _).obj (restrictionHomH0 f E) where
  app e := poweredIdealStageComparison f E e.unop.unop
  naturality _ _ g := poweredIdealStageComparison_naturality f E g

/-- The canonical morphism from the colimit of `Hom(Iₑ, E)` to `H⁰(U, E)`. -/
noncomputable def homColimitToOpenH0 {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace) :
    colimit (homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E) ⟶
      restrictionHomH0 f E :=
  colimit.desc (homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E)
    (Cocone.mk (restrictionHomH0 f E) (poweredIdealComparison f E))

/-- The colimit comparison restricts to the specified map at every powered stage. -/
theorem homColimitToOpenH0_ι {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (E : ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
    (e : (ℕᵒᵖ)ᵒᵖ) :
    colimit.ι (homDiagram (derivedIdealSystem f ⋙ affineDerivedTilde A) E) e ≫
      homColimitToOpenH0 f E = poweredIdealStageComparison f E e.unop.unop := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

end
