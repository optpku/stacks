module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Complex
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous.Exactness
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.Algebra.Homology.CochainComplex.KFlat

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X

/-- The stalkwise K-flatness predicate can be read directly on the canonical mapped complex. -/
@[simp] theorem stalkComplex_isKFlat_iff_mapHomologicalComplex_obj_isKFlat
    (K : CochainComplex ModX ℤ) (x : X) :
    (stalkComplex K x).IsKFlat ↔
      ((((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).obj K)).IsKFlat := by
  rfl

/-- Helper for Lemma 20.26.4: exactness is stable under composing two exact functors. -/
private theorem exactFunctorComp
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {D : Type*} [Category D]
    {F : A ⥤ B} {G : B ⥤ D}
    (hF : exactFunctor A B F)
    (hG : exactFunctor B D G) :
    exactFunctor A D (F ⋙ G) := by
  -- Proof comment: exactness is finite-limit and finite-colimit preservation, and both
  -- preservation properties compose.
  rw [CategoryTheory.exactFunctor_iff] at hF hG ⊢
  let _ : Limits.PreservesFiniteLimits F := hF.1
  let _ : Limits.PreservesFiniteColimits F := hF.2
  let _ : Limits.PreservesFiniteLimits G := hG.1
  let _ : Limits.PreservesFiniteColimits G := hG.2
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 20.26.4: exactness transports across a natural isomorphism of functors. -/
private theorem exactFunctorOfNatIso
    {A : Type*} [Category A]
    {B : Type*} [Category B]
    {F G : A ⥤ B}
    (e : F ≅ G) :
    exactFunctor A B F → exactFunctor A B G := by
  intro hF
  -- Proof comment: transport finite-limit and finite-colimit preservation across the natural
  -- isomorphism, then repackage the result as exactness.
  rw [CategoryTheory.exactFunctor_iff] at hF ⊢
  let _ : Limits.PreservesFiniteLimits F := hF.1
  let _ : Limits.PreservesFiniteColimits F := hF.2
  exact ⟨
    CategoryTheory.Limits.preservesFiniteLimits_of_natIso e,
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso e
  ⟩

section

variable [MonoidalPreadditive (RingedSpace.Modules X)]

/-- Helper for Lemma 20.26.4: realize a stalk module as the canonical module sheaf on the
one-point ringed space `({x}, \mathcal O_{X, x})`. -/
private noncomputable abbrev pointModuleSheafFunctor
    (x : X) :
    ModuleCat (X.presheaf.stalk x) ⥤ RingedSpace.Modules (pointRingedSpace x) :=
  RingedPoint.Module.functor (X.presheaf.stalk x)

/-- Helper for Lemma 20.26.4: taking the stalk complex at `x` preserves acyclicity of a complex
of `𝒪_X`-modules. -/
private theorem stalkComplex_acyclic_of_acyclic
    (M : CochainComplex ModX ℤ) (hM : M.Acyclic) (x : X) :
    (stalkComplex M x).Acyclic := by
  -- Proof comment: acyclicity is degreewise exactness, and exactness of a short complex of
  -- `𝒪_X`-modules can be checked stalkwise by Lemma `17.3.1`.
  rw [HomologicalComplex.acyclic_iff] at hM ⊢
  intro n
  change (RingedSpace.moduleStalkShortComplex (M.sc n) x).Exact
  exact RingedSpace.moduleStalkShortComplex_exact (M.sc n) x (hM n)

/-- Helper for Lemma 20.26.4: taking stalks commutes with tensoring a sheaf module on the right. -/
private noncomputable def stalkTensorRightComparisonIso
    (x : X) (ℱ : ModX) :
    tensorRight ℱ ⋙ RingedSpace.stalkModuleFunctor x ≅
      RingedSpace.stalkModuleFunctor x ⋙
        tensorRight (RingedSpace.stalkModuleCat ℱ x) :=
  NatIso.ofComponents
    (fun 𝒢 ↦ RingedSpace.Tensor.Stalk.comparisonIso 𝒢 ℱ x)
    (fun {𝒢 𝒢'} φ ↦ by
      -- Proof comment: functoriality is exactly the imported tensor/stalk naturality square,
      -- specialized to the identity on the fixed right tensor factor `ℱ`. The remaining
      -- transport blocker is to rewrite the source-side `moduleStalkHom x (φ ▷ ℱ)` and the
      -- target-side `tensorRight` map into a common normal form before applying
      -- `RingedSpace.Tensor.Stalk.comparison_naturality`.
      sorry)

/-- Helper for Lemma 20.26.4: after fixing the right tensor factor, the stalk/tensor comparison
extends degreewise to cochain complexes. -/
private noncomputable def stalkTensorRightComplexIso
    (x : X) (ℱ : ModX) (K : CochainComplex ModX ℤ) :
    (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).obj
      (((tensorRight ℱ).mapHomologicalComplex (up ℤ)).obj K)) ≅
      (((tensorRight (RingedSpace.stalkModuleCat ℱ x)).mapHomologicalComplex (up ℤ)).obj
        (stalkComplex K x)) :=
  -- Proof comment: apply the functor-level tensor/stalk comparison degreewise along the complex
  -- `K`.
  (NatIso.mapHomologicalComplex (stalkTensorRightComparisonIso (X := X) x ℱ) (up ℤ)).app K

/-- Helper for Lemma 20.26.4: the stalked tensor bicomplex underlying `M ⊗ K`. -/
private abbrev stalkTensorObjBicomplexSource
    (M K : CochainComplex ModX ℤ) (x : X) :=
  (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj
      ((((curriedTensor ModX).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj M).obj K)

/-- Helper for Lemma 20.26.4: the tensor bicomplex built from the stalk complexes of `M` and
`K`. -/
private abbrev stalkTensorObjBicomplexTarget
    (M K : CochainComplex ModX ℤ) (x : X) :=
  ((((curriedTensor (ModuleCat (X.presheaf.stalk x))).mapBifunctorHomologicalComplex
    (up ℤ) (up ℤ)).obj (stalkComplex M x)).obj (stalkComplex K x))

/-- Helper for Lemma 20.26.4: the columnwise stalk/tensor comparisons assemble to an
isomorphism between the two tensor bicomplexes. -/
private noncomputable def stalkTensorObjBicomplexIso
    (M K : CochainComplex ModX ℤ) (x : X) :
    stalkTensorObjBicomplexSource (X := X) M K x ≅
      stalkTensorObjBicomplexTarget (X := X) M K x :=
  -- Proof comment: the component in outer degree `q` is `stalkTensorRightComplexIso x (M.X q) K`;
  -- the remaining verification is the naturality of these components against the outer
  -- differential.
  sorry

/-- Helper for Lemma 20.26.4: the point-space realization functor on the one-point ringed space
is exact. -/
private theorem pointModuleSheafFunctorExact
    (x : X) :
    exactFunctor
      (ModuleCat (X.presheaf.stalk x))
      (RingedSpace.Modules (pointRingedSpace x))
      (pointModuleSheafFunctor (X := X) x) := by
  -- Proof comment: if the point-space module functor already carries the standard finite
  -- limit/colimit preservation instances, `ExactFunctor.of` packages the exactness directly.
  -- TODO: package the one-point-space equivalence given by evaluation on `⊤` and transport
  -- exactness across that equivalence; `ExactFunctor.of` does not synthesize the needed finite
  -- limit/colimit instances here.
  sorry

/-- Helper for Lemma 20.26.4: taking the stalk functor commutes with totalization of a
cohomological tensor bicomplex. -/
private abbrev stalkMappedBicomplex
    (x : X) (B : HomologicalComplex₂ ModX (up ℤ) (up ℤ)) :
    HomologicalComplex₂ (ModuleCat (X.presheaf.stalk x)) (up ℤ) (up ℤ) :=
  (((RingedSpace.stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj B

/-- Helper for Lemma 20.26.4: taking the stalk functor commutes with totalization of a
cohomological tensor bicomplex. -/
private noncomputable def stalkTotalTensorBicomplexIso
    (x : X) (B : HomologicalComplex₂ ModX (up ℤ) (up ℤ))
    [B.HasTotal (up ℤ)]
    [(stalkMappedBicomplex (X := X) x B).HasTotal (up ℤ)] :
    stalkComplex (HomologicalComplex₂.total B (up ℤ)) x ≅
      HomologicalComplex₂.total (stalkMappedBicomplex (X := X) x B) (up ℤ) := by
  -- Route correction: the remaining tensor/stalk normalization is no longer degreewise. The
  -- unresolved part is the generic coproduct comparison showing that `stalkModuleFunctor x`
  -- commutes with the totalization coproducts and their induced differential.
  -- TODO: copy the `restrictScalars_total_tensorBicomplexIso` proof pattern from
  -- `Lemma_15_59_3`, replacing restriction of scalars by `stalkModuleFunctor x`.
  sorry

/-- Helper for Lemma 20.26.4: taking stalks commutes with the totalized tensor product of
cochain complexes. -/
private noncomputable def stalkTensorObjIso
    (M K : CochainComplex ModX ℤ) (x : X)
    [HomologicalComplex.HasTensor M K]
    [HomologicalComplex.HasTensor (stalkComplex M x) (stalkComplex K x)] :
    stalkComplex (HomologicalComplex.tensorObj M K) x ≅
      HomologicalComplex.tensorObj (stalkComplex M x) (stalkComplex K x) := by
  -- Route correction: the tensor of cochain complexes is the totalization of the tensor
  -- bicomplex. The degreewise tensor/stalk transport is now isolated in
  -- `stalkTensorObjBicomplexIso`. The remaining blocker is the generic totalization bridge
  -- `stalkTotalTensorBicomplexIso`; once that coproduct comparison is proved, this theorem is the
  -- short composition sketched in the previous attempt.
  sorry

/-- Lemma 20.26.4: a complex `K` of `𝒪_X`-modules is K-flat if and only if, for every point
`x : X`, the induced stalk complex of `𝒪_{X, x}`-modules is K-flat. -/
@[stacks 06YB]
theorem isKFlat_iff_stalkwise_isKFlat (K : CochainComplex ModX ℤ) :
    K.IsKFlat ↔ ∀ x : X, (stalkComplex K x).IsKFlat := by
  -- Route correction: the proof is now split into two explicit frontiers. The easy direction
  -- reduces to the totalized tensor/stalk comparison `stalkTensorObjIso`, whose degreewise
  -- bicomplex part has been isolated above, while the hard direction reduces to the one-point
  -- exact globalization package centered on `pointModuleSheafFunctorExact`.
  -- TODO: compose `stalkTensorObjBicomplexIso` with `stalkTotalTensorBicomplexIso` for the easy
  -- direction, and globalize an acyclic local test complex via `RingedSpace.Module.Skyscraper.atPoint x` for the
  -- reverse direction.
  sorry

/-- If a complex of `𝒪_X`-modules is K-flat, then each stalk complex is K-flat. -/
theorem stalkComplex_isKFlat_of_isKFlat
    (K : CochainComplex ModX ℤ) (hK : K.IsKFlat) (x : X) :
    (stalkComplex K x).IsKFlat :=
  (isKFlat_iff_stalkwise_isKFlat K).mp hK x

/-- If every stalk complex of a complex of `𝒪_X`-modules is K-flat, then the complex is
K-flat. -/
theorem isKFlat_of_stalkComplex_isKFlat
    (K : CochainComplex ModX ℤ)
    (hK : ∀ x : X, (stalkComplex K x).IsKFlat) :
    K.IsKFlat :=
  (isKFlat_iff_stalkwise_isKFlat K).mpr hK

end

end AlgebraicGeometry.RingedSpace
