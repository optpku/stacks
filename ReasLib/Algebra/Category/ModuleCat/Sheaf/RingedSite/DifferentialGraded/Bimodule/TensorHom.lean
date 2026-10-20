module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule.Bimod
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Closed
public import ReasLib.CategoryTheory.Monoidal.Bimod.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-Hom adjunction for differential graded bimodule sheaves

This file specializes the generic relative internal Hom for bimodule objects to differential
graded modules and bimodules on a ringed site.  The inputs remain the source-facing DG objects,
while all tensor, internal-Hom, adjunction, and naturality data comes from the reusable
`CategoryTheory.Bimod` layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedBimodule.TensorHom

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The balanced tensor product of a right DG `A`-module and a DG `(A, B)`-bimodule, represented
as Mathlib's coequalizer-based right `B.toMon`-module. -/
@[stacks 0FRS "differential graded relative tensor product"]
noncomputable abbrev tensor {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, d)) (N : Mod(𝒜, 𝒝, d)) :
    CategoryTheory.Bimod.RightModule 𝒝.toMon :=
  (Bimod.tensorWith N.toBimod).obj M.toBimod

/-- The relative DG internal Hom from an `(A, B)`-bimodule to a right `B`-module, represented
as the canonical right `A.toMon`-module of `B`-linear internal maps. -/
@[stacks 0FRS "differential graded relative internal Hom"]
noncomputable abbrev internalHom {𝒜 𝒝 : DGA(𝒪)}
    (N : Mod(𝒜, 𝒝, d)) (L : Mod(𝒝, d)) :
    CategoryTheory.Bimod.RightModule 𝒜.toMon :=
  (Bimod.InternalHom.functor Cochain.rightInternalHom N.toBimod).obj L.toBimod

/-- The DG internal-Hom complex between two right modules over the same differential graded
algebra, obtained by forgetting the residual trivial-monoid action. -/
@[stacks 0FRS "differential graded module internal-Hom complex"]
noncomputable abbrev homComplex {𝒜 : DGA(𝒪)}
    (M L : CategoryTheory.Bimod.RightModule 𝒜.toMon) :
    CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ :=
  ((Bimod.InternalHom.functor Cochain.rightInternalHom M).obj L).X

/-- Lemma 24.17.3 (1) (0FRS), Hom-set form: relative tensoring with `N` is represented by the
relative DG internal Hom from `N`. -/
@[stacks 0FRS "differential graded tensor-Hom equivalence"]
noncomputable abbrev homEquiv {𝒜 𝒝 : DGA(𝒪)}
    (M : Mod(𝒜, d)) (N : Mod(𝒜, 𝒝, d)) (L : Mod(𝒝, d)) :
    (tensor M N ⟶ L.toBimod) ≃ (M.toBimod ⟶ internalHom N L) :=
  Bimod.InternalHom.homEquiv Cochain.rightInternalHom N.toBimod M.toBimod L.toBimod

/-- The differential graded relative tensor functor is left adjoint to the relative
internal-Hom functor. -/
@[stacks 0FRS "differential graded tensor-Hom adjunction"]
noncomputable abbrev adjunction {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    Bimod.tensorWith N.toBimod ⊣
      Bimod.InternalHom.functor Cochain.rightInternalHom N.toBimod :=
  Bimod.InternalHom.adjunction Cochain.rightInternalHom N.toBimod

/-- Lemma 24.17.3 (2) (0FRS), internal-Hom form: the DG internal-Hom complex out of a balanced
tensor product is canonically isomorphic to the iterated relative internal-Hom complex. -/
@[stacks 0FRS "differential graded internal-Hom currying"]
noncomputable def internalHomIso {𝒜 𝒝 : DGA(𝒪)}
    (M : Mod(𝒜, d)) (N : Mod(𝒜, 𝒝, d)) (L : Mod(𝒝, d)) :
    homComplex (tensor M N) L.toBimod ≅ homComplex M.toBimod (internalHom N L) :=
  (Bimod.forget (Mon.trivial
    (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ))).mapIso
      (Bimod.InternalHom.tensorIso Cochain.rightInternalHom
        M.toBimod N.toBimod L.toBimod)

/-- The DG tensor-Hom equivalence is natural contravariantly in the right `A`-module. -/
@[stacks 0FRS "differential graded tensor-Hom source naturality"]
theorem homEquiv_natural_source {𝒜 𝒝 : DGA(𝒪)} {M' M : Mod(𝒜, d)}
    (f : M' ⟶ M) (N : Mod(𝒜, 𝒝, d)) (L : Mod(𝒝, d))
    (g : tensor M N ⟶ L.toBimod) :
    homEquiv M' N L
        ((Bimod.tensorWith N.toBimod).map
          (DifferentialGradedModule.toBimodMap f) ≫ g) =
      DifferentialGradedModule.toBimodMap f ≫ homEquiv M N L g := sorry

/-- The DG tensor-Hom equivalence is natural covariantly in the right `B`-module target. -/
@[stacks 0FRS "differential graded tensor-Hom target naturality"]
theorem homEquiv_natural_target {𝒜 𝒝 : DGA(𝒪)}
    (M : Mod(𝒜, d)) (N : Mod(𝒜, 𝒝, d)) {L L' : Mod(𝒝, d)}
    (f : tensor M N ⟶ L.toBimod) (g : L ⟶ L') :
    homEquiv M N L' (f ≫ DifferentialGradedModule.toBimodMap g) =
      homEquiv M N L f ≫
        (Bimod.InternalHom.functor Cochain.rightInternalHom N.toBimod).map
          (DifferentialGradedModule.toBimodMap g) := sorry

/-- The DG tensor-Hom equivalence is natural contravariantly in the bimodule. -/
@[stacks 0FRS "differential graded tensor-Hom bimodule naturality"]
theorem homEquiv_natural_bimodule {𝒜 𝒝 : DGA(𝒪)}
    (M : Mod(𝒜, d)) {N N' : Mod(𝒜, 𝒝, d)} (f : N ⟶ N')
    (L : Mod(𝒝, d)) (g : tensor M N' ⟶ L.toBimod) :
    homEquiv M N L
        ((Bimod.InternalHom.tensorMap
          (DifferentialGradedBimodule.toBimodMap f)).app M.toBimod ≫ g) =
      homEquiv M N' L g ≫
        (Bimod.InternalHom.pre Cochain.rightInternalHom
          (DifferentialGradedBimodule.toBimodMap f)).app L.toBimod := sorry

/-- Internal-Hom currying is natural contravariantly in the right `A`-module, as an equality of
morphisms of cochain complexes. -/
@[stacks 0FRS "differential graded internal-Hom source naturality"]
theorem internalHomIso_natural_source {𝒜 𝒝 : DGA(𝒪)} {M M' : Mod(𝒜, d)}
    (f : M ⟶ M') (N : Mod(𝒜, 𝒝, d)) (L : Mod(𝒝, d)) :
    (internalHomIso M' N L).hom ≫
        ((Bimod.InternalHom.pre Cochain.rightInternalHom
          (DifferentialGradedModule.toBimodMap f)).app (internalHom N L)).hom =
      ((Bimod.InternalHom.pre Cochain.rightInternalHom
        (Bimod.whiskerRight (DifferentialGradedModule.toBimodMap f) N.toBimod)).app
          L.toBimod).hom ≫ (internalHomIso M N L).hom := sorry

/-- Internal-Hom currying is natural contravariantly in the DG bimodule, as an equality of
morphisms of cochain complexes. -/
@[stacks 0FRS "differential graded internal-Hom bimodule naturality"]
theorem internalHomIso_natural_bimodule {𝒜 𝒝 : DGA(𝒪)}
    (M : Mod(𝒜, d)) {N N' : Mod(𝒜, 𝒝, d)} (f : N ⟶ N')
    (L : Mod(𝒝, d)) :
    (internalHomIso M N' L).hom ≫
        ((Bimod.InternalHom.functor Cochain.rightInternalHom M.toBimod).map
          ((Bimod.InternalHom.pre Cochain.rightInternalHom
            (DifferentialGradedBimodule.toBimodMap f)).app L.toBimod)).hom =
      ((Bimod.InternalHom.pre Cochain.rightInternalHom
        (Bimod.whiskerLeft M.toBimod
          (DifferentialGradedBimodule.toBimodMap f))).app L.toBimod).hom ≫
        (internalHomIso M N L).hom := sorry

/-- Internal-Hom currying is natural covariantly in the right `B`-module target, as an equality
of morphisms of cochain complexes. -/
@[stacks 0FRS "differential graded internal-Hom target naturality"]
theorem internalHomIso_natural_target {𝒜 𝒝 : DGA(𝒪)}
    (M : Mod(𝒜, d)) (N : Mod(𝒜, 𝒝, d)) {L L' : Mod(𝒝, d)}
    (f : L ⟶ L') :
    ((Bimod.InternalHom.functor Cochain.rightInternalHom (tensor M N)).map
      (DifferentialGradedModule.toBimodMap f)).hom ≫ (internalHomIso M N L').hom =
      (internalHomIso M N L).hom ≫
        ((Bimod.InternalHom.functor Cochain.rightInternalHom M.toBimod).map
          ((Bimod.InternalHom.functor Cochain.rightInternalHom N.toBimod).map
            (DifferentialGradedModule.toBimodMap f))).hom := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedBimodule.TensorHom

end
