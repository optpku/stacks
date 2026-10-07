module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule

/-!
# Endomorphism actions on differential graded module sheaves

This leaf owns the degreewise presentation of a morphism from a differential graded algebra
sheaf to the right-linear endomorphisms of a fixed differential graded module sheaf. It also
identifies these actions with bimodule structures having the prescribed right module.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedBimodule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The degreewise presentation of a morphism from `𝒜` to the differential graded algebra of
right-`𝒝`-linear endomorphisms of `N`. -/
@[stacks 0FRR, ext]
structure ActionOn (𝒜 : DGA(𝒪)) {𝒝 : DGA(𝒪)} (N : Mod(𝒝, d)) where
  /-- The homogeneous action map of bidegree `(n, m)`. -/
  map (n m : ℤ) :
    𝒜.toComplex.X n ⊗ N.toComplex.X m ⟶ N.toComplex.X (n + m)
  /-- Multiplication in `𝒜` acts by composition. -/
  map_mul :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (𝒜.toComplex.X j) (N.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ map j k) ≫ map i (j + k) =
        (𝒜.mul i j ▷ N.toComplex.X k) ≫ map (i + j) k ≫
          eqToHom (congrArg N.toComplex.X (Int.add_assoc i j k))
  /-- The action maps are right `𝒝`-linear. -/
  comm_rightMul :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (N.toComplex.X j) (𝒝.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ N.smul j k) ≫ map i (j + k) =
        (map i j ▷ 𝒝.toComplex.X k) ≫ N.smul (i + j) k ≫
          eqToHom (congrArg N.toComplex.X (Int.add_assoc i j k))
  /-- The unit of `𝒜` acts by the identity. -/
  map_one :
    ∀ n : ℤ,
      (λ_ (N.toComplex.X n)).hom =
        (𝒜.one ▷ N.toComplex.X n) ≫ map 0 n ≫
          eqToHom (congrArg N.toComplex.X (zero_add n))
  /-- The action is compatible with the differentials. -/
  comm_d :
    ∀ n m : ℤ,
      map n m ≫ N.toComplex.d (n + m) (n + m + 1) =
        ((𝒜.toComplex.d n (n + 1)) ▷ N.toComplex.X m) ≫ map (n + 1) m ≫
          eqToHom
            (congrArg N.toComplex.X
              ((Int.add_assoc n 1 m).trans
                ((congrArg (fun p : ℤ ↦ n + p) (Int.add_comm 1 m)).trans
                  (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          ((𝒜.toComplex.X n ◁ N.toComplex.d m (m + 1)) ≫ map n (m + 1) ≫
            eqToHom (congrArg N.toComplex.X (Int.add_assoc n m 1).symm))

namespace ActionOn

/-- An endomorphism action evaluates on its homogeneous action maps. -/
instance instCoeFun {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)} :
    CoeFun (ActionOn 𝒜 N) (fun _ ↦ ∀ n m : ℤ,
      𝒜.toComplex.X n ⊗ N.toComplex.X m ⟶ N.toComplex.X (n + m)) where
  coe τ := τ.map

/-- Coercion to a function is evaluation of the homogeneous action map. -/
@[simp] theorem coe_apply {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (τ : ActionOn 𝒜 N) (n m : ℤ) : τ n m = τ.map n m := sorry

/-- Package an endomorphism action as a differential graded bimodule sheaf. -/
def toBimodule {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)} (τ : ActionOn 𝒜 N) :
    Mod(𝒜, 𝒝, d) where
  toRightModule := N
  leftMul := τ.map
  left_assoc := τ.map_mul
  middle_assoc := τ.comm_rightMul
  one_left := τ.map_one
  d_leftMul := τ.comm_d

/-- The bimodule packaged from an action has the prescribed right module. -/
@[simp] theorem toBimodule_toRightModule {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (τ : ActionOn 𝒜 N) : τ.toBimodule.toRightModule = N := sorry

/-- The bimodule packaged from an action uses the given homogeneous action maps. -/
@[simp] theorem toBimodule_leftMul {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (τ : ActionOn 𝒜 N) (n m : ℤ) : τ.toBimodule.leftMul n m = τ n m := sorry

/-- Extract the endomorphism action carried by a differential graded bimodule sheaf. -/
def ofBimodule {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) :
    ActionOn 𝒜 M.toRightModule where
  map := M.leftMul
  map_mul := M.left_assoc
  comm_rightMul := M.middle_assoc
  map_one := M.one_left
  comm_d := M.d_leftMul

/-- Extracting an action from a bimodule recovers its left multiplication maps. -/
@[simp] theorem ofBimodule_apply {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d))
    (n m : ℤ) : ofBimodule M n m = M.leftMul n m := sorry

end ActionOn

/-- Differential graded `(𝒜, 𝒝)`-bimodule structures whose underlying right module is the
fixed module `N`. -/
abbrev FixedRight (𝒜 𝒝 : DGA(𝒪)) (N : Mod(𝒝, d)) :=
  { M : Mod(𝒜, 𝒝, d) // M.toRightModule = N }

namespace FixedRight

/-- A fixed-right bimodule structure coerces to its underlying bimodule. -/
instance instCoeOut {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)} :
    CoeOut (FixedRight 𝒜 𝒝 N) (Mod(𝒜, 𝒝, d)) where
  coe M := M.1

/-- Extract the endomorphism action on the prescribed right module. -/
def toAction {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)} (M : FixedRight 𝒜 𝒝 N) :
    ActionOn 𝒜 N :=
  M.2 ▸ ActionOn.ofBimodule M.1

/-- Extracting the fixed-right action recovers the transported left multiplication maps. -/
@[simp] theorem toAction_apply {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (M : FixedRight 𝒜 𝒝 N) (n m : ℤ) :
    M.toAction n m = M.2 ▸ M.1.leftMul n m := sorry

end FixedRight

namespace ActionOn

/-- Regard an endomorphism action as a bimodule structure on its fixed right module. -/
def toFixedRight {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)} (τ : ActionOn 𝒜 N) :
    FixedRight 𝒜 𝒝 N :=
  ⟨τ.toBimodule, rfl⟩

/-- The underlying bimodule of the fixed-right structure is the bimodule packaged from the
action. -/
@[simp] theorem toFixedRight_coe {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (τ : ActionOn 𝒜 N) :
    ((τ.toFixedRight : FixedRight 𝒜 𝒝 N) : Mod(𝒜, 𝒝, d)) = τ.toBimodule := sorry

end ActionOn

namespace FixedRight

/-- Fixed-right differential graded bimodule structures are equivalent to right-linear
endomorphism actions on the fixed module. -/
@[stacks 0FRR]
def actionEquiv (𝒜 𝒝 : DGA(𝒪)) (N : Mod(𝒝, d)) :
    FixedRight 𝒜 𝒝 N ≃ ActionOn 𝒜 N where
  toFun := toAction
  invFun := ActionOn.toFixedRight
  left_inv := sorry
  right_inv := sorry

/-- The forward map of `actionEquiv` extracts the fixed-right action. -/
@[simp] theorem actionEquiv_apply {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (M : FixedRight 𝒜 𝒝 N) : actionEquiv 𝒜 𝒝 N M = M.toAction := sorry

/-- The inverse map of `actionEquiv` packages an action as a fixed-right bimodule. -/
@[simp] theorem actionEquiv_symm_apply {𝒜 𝒝 : DGA(𝒪)} {N : Mod(𝒝, d)}
    (τ : ActionOn 𝒜 N) :
    (actionEquiv 𝒜 𝒝 N).symm τ = τ.toFixedRight := sorry

end FixedRight

end

end SheafOfModules.RingedSite.DifferentialGradedBimodule
