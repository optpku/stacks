module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Quotient

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace

noncomputable section

universe u

namespace ModuleCech.LocalCohomology

variable {X : Scheme.{u}}

/-- The degree-`c` cohomology of the principal-open Čech complex after passage to ambient
ringed-space modules. -/
noncomputable def cechCohomologyFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ X.toRingedSpace.Modules :=
  ModuleCech.ofSectionsFunctor f ⋙
    (Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ) ⋙
    HomologicalComplex.homologyFunctor X.toRingedSpace.Modules (up ℕ) c

/-- Evaluation of `cechCohomologyFunctor` is degree-`c` homology of the mapped Čech complex. -/
theorem cechCohomologyFunctor_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (cechCohomologyFunctor f).obj ℱ =
      (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).homology c := sorry

/-- The canonical inclusion into `ULift` is strictly monotone. -/
theorem fullTuple_strictMono (n : ℕ) :
    StrictMono (fun i : Fin (n + 1) ↦ ULift.up i) := sorry

/-- The canonical full ordered tuple indexing the top nonzero Čech summand. -/
def fullTuple (n : ℕ) : OrderedCechIndex (ULift.{u} (Fin (n + 1))) n :=
  OrderEmbedding.ofStrictMono (fun i ↦ ULift.up i) (fullTuple_strictMono n)

/-- The numerator map sends a section to its restriction over the full intersection, with a
separate degree-zero branch for the empty family. -/
noncomputable def numeratorTerm {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (Scheme.Modules.toRingedSpace X).obj ℱ ⟶
      (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).X c :=
  match c, f with
  | 0, f =>
      (Scheme.Modules.toRingedSpace X).map
        (eqToHom (ModuleCech.ofSections_X_zero f ℱ).symm)
  | n + 1, f =>
      (Scheme.Modules.toRingedSpace X).map
        ((RingedSpace.OpenSubspace.Pushforward.adjunction X.toRingedSpace
              (TopCat.Presheaf.Cech.intersection
                (fun i : ULift.{u} (Fin (n + 1)) ↦ X.basicOpen (f i.down))
                (fullTuple n).toFun)).unit.app ℱ ≫
          biproduct.ι
            (fun σ : OrderedCechIndex (ULift.{u} (Fin (n + 1))) n ↦
              AlgebraicGeometry.Scheme.ModuleCech.Ordered.summand
                (fun i : ULift.{u} (Fin (n + 1)) ↦ X.basicOpen (f i.down)) ℱ n σ)
            (fullTuple n) ≫
          eqToHom (ModuleCech.ofSections_X_succ f ℱ n).symm)

/-- The top numerator map is a degree-`c` cycle. -/
theorem numeratorTerm_comp_d {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    numeratorTerm f ℱ ≫
      (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).d c (c + 1) = 0 := sorry

/-- The canonical cycle represented by the numerator over the full Čech intersection. -/
noncomputable def numeratorCycleApp {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    (Scheme.Modules.toRingedSpace X).obj ℱ ⟶
      (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
        (ModuleCech.ofSections f ℱ)).cycles c :=
  let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
    (ModuleCech.ofSections f ℱ)
  K.liftCycles (numeratorTerm f ℱ) (c + 1) (CochainComplex.next ℕ c)
    (numeratorTerm_comp_d f ℱ)

/-- The degree-`c` Čech class of the numerator `s/(∏ i, f i)`. -/
noncomputable def numeratorClassApp {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    (Scheme.Modules.toRingedSpace X).obj ℱ ⟶ (cechCohomologyFunctor f).obj ℱ :=
  numeratorCycleApp f ℱ ≫
    (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
      (ModuleCech.ofSections f ℱ)).homologyπ c

/-- Numerator classes are natural in the coefficient module sheaf. -/
theorem numeratorClass_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (Scheme.Modules.toRingedSpace X).map φ ≫ numeratorClassApp f 𝒢 =
      numeratorClassApp f ℱ ≫ (cechCohomologyFunctor f).map φ := sorry

/-- The natural top Čech fraction class `s ↦ [s/(∏ i, f i)]`. -/
noncomputable def numeratorClass {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    Scheme.Modules.toRingedSpace X ⟶ cechCohomologyFunctor f where
  app ℱ := numeratorClassApp f ℱ
  naturality _ _ φ := numeratorClass_naturality f φ

/-- For a nonempty family, the cycle representative of `numeratorClass` is restriction to the
summand indexed by the full ordered tuple. -/
theorem numeratorClass_fullTuple {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))
    (ℱ : X.Modules) :
    numeratorCycleApp f ℱ ≫
        (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
          (ModuleCech.ofSections f ℱ)).iCycles (n + 1) =
      numeratorTerm f ℱ := sorry

/-- For the empty family, the numerator class uses the canonical degree-zero cycle. -/
theorem numeratorClass_zero (f : Fin 0 → Γ(X, ⊤)) (ℱ : X.Modules) :
    numeratorCycleApp f ℱ ≫
        (((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
          (ModuleCech.ofSections f ℱ)).iCycles 0 =
      numeratorTerm f ℱ := sorry

/-- Multiplication by the chosen sections kills the top Čech numerator class. -/
theorem sectionMultiplication_comp_numeratorClass {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    sectionMultiplication f ℱ ≫ (numeratorClass f).app ℱ = 0 := sorry

/-- The top Čech class descended through the finite-family cokernel. -/
noncomputable def cechClassApp {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (quotientFunctor f).obj ℱ ⟶ (cechCohomologyFunctor f).obj ℱ :=
  cokernel.desc (sectionMultiplication f ℱ) (numeratorClassApp f ℱ)
    (sectionMultiplication_comp_numeratorClass f ℱ)

/-- The descended top Čech class is natural in the coefficient module sheaf. -/
theorem cechClass_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (quotientFunctor f).map φ ≫ cechClassApp f 𝒢 =
      cechClassApp f ℱ ≫ (cechCohomologyFunctor f).map φ := sorry

/-- The natural top Čech class on the finite-family quotient. -/
noncomputable def cechClass {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    quotientFunctor f ⟶ cechCohomologyFunctor f where
  app ℱ := cechClassApp f ℱ
  naturality _ _ φ := cechClass_naturality f φ

/-- The cokernel projection followed by `cechClass` is the numerator fraction class. -/
theorem cechClass_π {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (quotientProjection f).app ℱ ≫ (cechClass f).app ℱ =
      (numeratorClass f).app ℱ := sorry

end ModuleCech.LocalCohomology

end
