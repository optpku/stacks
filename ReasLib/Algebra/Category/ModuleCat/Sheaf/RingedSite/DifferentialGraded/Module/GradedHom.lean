module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Preadditive

/-!
# Graded Hom objects for differential graded module sheaves

This leaf owns homogeneous right-linear maps between differential graded module sheaves and the
standard Hom differential, identity, and composition. The DG-category instance is installed in a
separate leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Reassociate the target degree in the action law for a homogeneous map. -/
theorem gradedHom_action_index (n m k : ℤ) :
    (n + k) + m = (n + m) + k := sorry

/-- Reassociate the target of the post-differential term in the Hom differential. -/
theorem gradedHom_differential_left_index (n k : ℤ) :
    (n + k) + 1 = n + (k + 1) := sorry

/-- Reassociate the target of the pre-differential term in the Hom differential. -/
theorem gradedHom_differential_right_index (n k : ℤ) :
    (n + 1) + k = n + (k + 1) := sorry

/-- Reassociate the target degree of a composite of homogeneous maps. -/
theorem gradedHom_comp_index (n i j : ℤ) :
    (n + i) + j = n + (i + j) := sorry

/-- A degree-`k` homogeneous right-linear map between differential graded module sheaves. -/
@[ext]
structure GradedHom (𝒜 : DGA(𝒪)) (L M : Mod(𝒜, d)) (k : ℤ) where
  /-- The degreewise maps, shifting the target degree by `k`. -/
  hom : ∀ n : ℤ, L.toComplex.X n ⟶ M.toComplex.X (n + k)
  /-- Compatibility with the right action of the differential graded algebra. -/
  comm :
    ∀ n m : ℤ,
      L.smul n m ≫ hom (n + m) =
        (hom n ▷ 𝒜.toComplex.X m) ≫
          M.smul (n + k) m ≫
          eqToHom
            (congrArg M.toComplex.X (gradedHom_action_index n m k))

/-- A homogeneous map evaluates to its degreewise family. -/
instance gradedHomCoeFun {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} {k : ℤ} :
    CoeFun (GradedHom 𝒜 L M k)
      (fun _ ↦ ∀ n : ℤ, L.toComplex.X n ⟶ M.toComplex.X (n + k)) where
  coe f := f.hom

/-- Evaluation of a homogeneous map is its stored degreewise map. -/
@[simp]
theorem gradedHom_coe_apply {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} {k : ℤ}
    (f : GradedHom 𝒜 L M k) (n : ℤ) :
    f n = f.hom n := sorry

/-- The degreewise family determines a homogeneous map. -/
theorem gradedHom_hom_injective {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} {k : ℤ} :
    Function.Injective (fun f : GradedHom 𝒜 L M k ↦ f.hom) := sorry

/-- The zero homogeneous map is zero in every degree. -/
instance gradedHomZero {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    Zero (GradedHom 𝒜 L M k) where
  zero :=
    { hom := fun _ ↦ 0
      comm := sorry }

/-- Addition of homogeneous maps is computed degreewise. -/
instance gradedHomAdd {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    Add (GradedHom 𝒜 L M k) where
  add f g :=
    { hom := fun n ↦ f.hom n + g.hom n
      comm := sorry }

/-- Negation of homogeneous maps is computed degreewise. -/
instance gradedHomNeg {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    Neg (GradedHom 𝒜 L M k) where
  neg f :=
    { hom := fun n ↦ -f.hom n
      comm := sorry }

/-- Subtraction of homogeneous maps is computed degreewise. -/
instance gradedHomSub {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    Sub (GradedHom 𝒜 L M k) where
  sub f g :=
    { hom := fun n ↦ f.hom n - g.hom n
      comm := sorry }

/-- Natural scalar multiplication of homogeneous maps is computed degreewise. -/
instance gradedHomSMulNat {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    SMul ℕ (GradedHom 𝒜 L M k) where
  smul a f :=
    { hom := fun n ↦ a • f.hom n
      comm := sorry }

/-- Integer scalar multiplication of homogeneous maps is computed degreewise. -/
instance gradedHomSMulInt {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    SMul ℤ (GradedHom 𝒜 L M k) where
  smul a f :=
    { hom := fun n ↦ a • f.hom n
      comm := sorry }

/-- Homogeneous right-linear maps form an additive commutative group. -/
instance gradedHomAddCommGroup {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k : ℤ) :
    AddCommGroup (GradedHom 𝒜 L M k) :=
  Function.Injective.addCommGroup
    (fun f : GradedHom 𝒜 L M k ↦ f.hom)
    gradedHom_hom_injective
    sorry
    (fun _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ _ ↦ sorry)
    (fun _ _ ↦ sorry)
    (fun _ _ ↦ sorry)

/-- The zero homogeneous map evaluates to zero. -/
@[simp]
theorem gradedHom_zero_apply {𝒜 : DGA(𝒪)} (L M : Mod(𝒜, d)) (k n : ℤ) :
    (0 : GradedHom 𝒜 L M k).hom n = 0 := sorry

/-- A sum of homogeneous maps is evaluated degreewise. -/
@[simp]
theorem gradedHom_add_apply {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} {k : ℤ}
    (f g : GradedHom 𝒜 L M k) (n : ℤ) :
    (f + g).hom n = f.hom n + g.hom n := sorry

/-- The differential on the graded Hom object. -/
def gradedHomDifferential {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} (k : ℤ) :
    GradedHom 𝒜 L M k → GradedHom 𝒜 L M (k + 1) :=
  fun f ↦
    { hom := fun n ↦
        f.hom n ≫
            M.toComplex.d (n + k) (n + k + 1) ≫
            eqToHom
              (congrArg M.toComplex.X
                (gradedHom_differential_left_index n k)) -
          k.negOnePow •
            (L.toComplex.d n (n + 1) ≫
              f.hom (n + 1) ≫
              eqToHom
                (congrArg M.toComplex.X
                  (gradedHom_differential_right_index n k)))
      comm := sorry }

/-- The Hom differential is the signed commutator with the module differentials. -/
@[simp]
theorem gradedHomDifferential_apply
    {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)} (k : ℤ)
    (f : GradedHom 𝒜 L M k) (n : ℤ) :
    (gradedHomDifferential k f).hom n =
      f.hom n ≫
          M.toComplex.d (n + k) (n + k + 1) ≫
          eqToHom
            (congrArg M.toComplex.X
              (gradedHom_differential_left_index n k)) -
        k.negOnePow •
          (L.toComplex.d n (n + 1) ≫
            f.hom (n + 1) ≫
            eqToHom
              (congrArg M.toComplex.X
                (gradedHom_differential_right_index n k))) := sorry

/-- The degree-zero identity homogeneous map. -/
def gradedHomId {𝒜 : DGA(𝒪)} (L : Mod(𝒜, d)) :
    GradedHom 𝒜 L L 0 where
  hom := fun n ↦ eqToHom (congrArg L.toComplex.X (add_zero n).symm)
  comm := sorry

/-- The homogeneous identity is the canonical degree-zero reindexing. -/
@[simp]
theorem gradedHomId_apply {𝒜 : DGA(𝒪)} (L : Mod(𝒜, d)) (n : ℤ) :
    (gradedHomId L).hom n =
      eqToHom (congrArg L.toComplex.X (add_zero n).symm) := sorry

/-- Composition of homogeneous right-linear maps. -/
def gradedHomComp {𝒜 : DGA(𝒪)} {K L M : Mod(𝒜, d)} {i j : ℤ}
    (g : GradedHom 𝒜 L M j) (f : GradedHom 𝒜 K L i) :
    GradedHom 𝒜 K M (i + j) where
  hom := fun n ↦
    f.hom n ≫
      g.hom (n + i) ≫
      eqToHom (congrArg M.toComplex.X (gradedHom_comp_index n i j))
  comm := sorry

/-- Homogeneous composition is computed degreewise. -/
@[simp]
theorem gradedHomComp_apply
    {𝒜 : DGA(𝒪)} {K L M : Mod(𝒜, d)} {i j : ℤ}
    (g : GradedHom 𝒜 L M j) (f : GradedHom 𝒜 K L i) (n : ℤ) :
    (gradedHomComp g f).hom n =
      f.hom n ≫
        g.hom (n + i) ≫
        eqToHom (congrArg M.toComplex.X (gradedHom_comp_index n i j)) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule
