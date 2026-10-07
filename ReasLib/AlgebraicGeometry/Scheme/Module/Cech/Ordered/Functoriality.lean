module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Ordered

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleCech.Ordered

variable {X : Scheme.{u}} {ι : Type u} [Fintype ι] [LinearOrder ι]

/-- A module morphism induces a morphism on an ordered Čech summand. -/
noncomputable def summandMap (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) (p : ℕ) (σ : OrderedCechIndex ι p) :
    summand 𝒰 ℱ p σ ⟶ summand 𝒰 𝒢 p σ :=
  AlgebraicGeometry.Scheme.openCoverModuleCechSummandMap 𝒰 φ p σ.toFun

/-- The diagonal finite-biproduct map induced on an ordered Čech term. -/
noncomputable def termMap (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) (p : ℕ) : term 𝒰 ℱ p ⟶ term 𝒰 𝒢 p :=
  biproduct.lift fun σ ↦
    biproduct.π (fun τ : OrderedCechIndex ι p ↦ summand 𝒰 ℱ p τ) σ ≫
      summandMap 𝒰 φ p σ

/-- The component maps induced by a module morphism on the extended ordered Čech complex. -/
noncomputable def extendedMapComponent (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) : ∀ n, (extended 𝒰 ℱ).X n ⟶ (extended 𝒰 𝒢).X n
  | 0 => φ
  | p + 1 => termMap 𝒰 φ p

/-- The component maps induced by a module morphism commute with the extended ordered Čech
differentials. -/
theorem extendedMapComponent_comm (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    extendedMapComponent 𝒰 φ i ≫ (extended 𝒰 𝒢).d i j =
      (extended 𝒰 ℱ).d i j ≫ extendedMapComponent 𝒰 φ j := sorry

/-- A module morphism induces the canonical morphism of extended ordered Čech complexes. -/
noncomputable def extendedMap (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) : extended 𝒰 ℱ ⟶ extended 𝒰 𝒢 :=
  HomologicalComplex.Hom.mk (extendedMapComponent 𝒰 φ)
    (extendedMapComponent_comm 𝒰 φ)

/-- The extended ordered Čech map induced by an identity is the identity. -/
theorem extendedMap_id (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    extendedMap 𝒰 (𝟙 ℱ) = 𝟙 (extended 𝒰 ℱ) := sorry

/-- Extended ordered Čech maps preserve composition. -/
theorem extendedMap_comp (𝒰 : ι → X.Opens) {ℱ 𝒢 ℋ : X.Modules}
    (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ ℋ) :
    extendedMap 𝒰 (φ ≫ ψ) = extendedMap 𝒰 φ ≫ extendedMap 𝒰 ψ := sorry

/-- The extended ordered Čech complex, functorial in its module argument. -/
noncomputable def extendedFunctor (𝒰 : ι → X.Opens) :
    X.Modules ⥤ CochainComplex X.Modules ℕ where
  obj ℱ := extended 𝒰 ℱ
  map φ := extendedMap 𝒰 φ
  map_id ℱ := extendedMap_id 𝒰 ℱ
  map_comp φ ψ := extendedMap_comp 𝒰 φ ψ

/-- The canonical projection from an extended ordered Čech complex to its degree-zero module. -/
noncomputable def projectionApp (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    extended 𝒰 ℱ ⟶ (CochainComplex.single₀ X.Modules).obj ℱ :=
  (CochainComplex.toSingle₀Equiv (extended 𝒰 ℱ) ℱ).symm (𝟙 ℱ)

/-- The degree-zero projections from extended ordered Čech complexes are natural in the module. -/
theorem projection_naturality (𝒰 : ι → X.Opens) {ℱ 𝒢 : X.Modules}
    (φ : ℱ ⟶ 𝒢) :
    extendedMap 𝒰 φ ≫ projectionApp 𝒰 𝒢 =
      projectionApp 𝒰 ℱ ≫ (CochainComplex.single₀ X.Modules).map φ := sorry

/-- The natural projection from the extended ordered Čech functor to modules concentrated in
degree zero. -/
noncomputable def projection (𝒰 : ι → X.Opens) :
    extendedFunctor 𝒰 ⟶ CochainComplex.single₀ X.Modules where
  app ℱ := projectionApp 𝒰 ℱ
  naturality _ _ φ := projection_naturality 𝒰 φ

end AlgebraicGeometry.Scheme.ModuleCech.Ordered

end
