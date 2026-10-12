/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.DifferentialGraded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact

/-!
# Mapping cones of differential graded module sheaves

This leaf owns the source-faithful mapping cone of a morphism of right differential graded module
sheaves on an arbitrary ringed site.  Its underlying cochain complex is compared explicitly with
Mathlib's canonical cochain-complex mapping cone.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open HomologicalComplex
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]

namespace DifferentialGradedModule

/-- The degree-`n` term in the textbook ordering for a mapping cone. -/
def mappingConeTerm
    {𝒜 : DGA(𝒪)} {K L : Mod(𝒜, d)}
    (n : ℤ) : ringedSiteModuleCategory J 𝒪 :=
  L.toComplex.X n ⊞ K.toComplex.X (n + 1)

section

variable {𝒜 : DGA(𝒪)} {K L : Mod(𝒜, d)}

/-- The canonical mapping-cone degree identifies with the textbook order
`L^n ⊞ K^(n + 1)` after swapping the canonical biproduct factors. -/
noncomputable def cochainMappingConeXIso
    (f : K ⟶ L) (n : ℤ) :
    (CochainComplex.mappingCone f.toCochainMap).X n ≅
      mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n :=
  homotopyCofiber.XIsoBiprod f.toCochainMap n (n + 1) rfl ≪≫
    biprod.braiding (K.toComplex.X (n + 1)) (L.toComplex.X n)

/-- The textbook-ordered differential on a mapping cone. -/
noncomputable def mappingConeDiff
    (f : K ⟶ L) (n : ℤ) :
    mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n ⟶
      mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) (n + 1) :=
  (cochainMappingConeXIso f n).inv ≫
    (CochainComplex.mappingCone f.toCochainMap).d n (n + 1) ≫
    (cochainMappingConeXIso f (n + 1)).hom

/-- The textbook-ordered mapping-cone differential squares to zero. -/
theorem mappingConeDiff_sq
    (f : K ⟶ L) :
    ∀ n : ℤ,
      mappingConeDiff (𝒜 := 𝒜) (K := K) (L := L) f n ≫
        mappingConeDiff (𝒜 := 𝒜) (K := K) (L := L) f (n + 1) = 0 := sorry

/-- The underlying cochain complex of a textbook-ordered mapping cone. -/
noncomputable def mappingConeComplex
    (f : K ⟶ L) : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ :=
  CochainComplex.of
    (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L))
    (mappingConeDiff (𝒜 := 𝒜) (K := K) (L := L) f)
    (mappingConeDiff_sq (𝒜 := 𝒜) (K := K) (L := L) f)

/-- The direct-sum `𝒜`-action on a textbook-ordered mapping-cone term. -/
noncomputable def mappingConeSmul
    (n m : ℤ) :
    tensorObj (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n) (𝒜.toComplex.X m) ⟶
      mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) (n + m) :=
  ((tensorRight (𝒜.toComplex.X m)).mapBiprod (L.toComplex.X n) (K.toComplex.X (n + 1))).hom ≫
    biprod.map
      (L.smul n m)
      (K.smul (n + 1) m ≫
        eqToHom
          (congrArg (fun t : ℤ ↦ K.toComplex.X t)
            (differentialGradedAlgebra_leftLeibniz_index n m)))

/-- The direct-sum mapping-cone action is associative. -/
theorem mappingCone_smul_assoc
    (n m k : ℤ) :
    (α_ (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n)
        (𝒜.toComplex.X m) (𝒜.toComplex.X k)).hom ≫
        (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n ◁ 𝒜.mul m k) ≫
        mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n (m + k) =
      (mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n m ▷ 𝒜.toComplex.X k) ≫
        mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) (n + m) k ≫
        eqToHom
          (congrArg (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L))
            (Int.add_assoc n m k)) := sorry

/-- The unit section of `𝒜^0` acts as the identity on each mapping-cone degree. -/
theorem mappingCone_one_smul
    (n : ℤ) :
    (ρ_ (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n)).hom =
      (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n ◁ 𝒜.one) ≫
        mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n 0 ≫
        eqToHom
          (congrArg (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L))
            (add_zero n)) := sorry

/-- The mapping-cone differential satisfies the Leibniz rule for the direct-sum action. -/
theorem mappingCone_d_smul
    (f : K ⟶ L) (n m : ℤ) :
    mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n m ≫
        mappingConeDiff (𝒜 := 𝒜) (K := K) (L := L) f (n + m) =
      (mappingConeDiff (𝒜 := 𝒜) (K := K) (L := L) f n ▷ 𝒜.toComplex.X m) ≫
        mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) (n + 1) m ≫
        eqToHom
          (congrArg (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L))
            (differentialGradedAlgebra_leftLeibniz_index n m)) +
      n.negOnePow •
        ((mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n ◁
            𝒜.toComplex.d m (m + 1)) ≫
          mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n (m + 1) ≫
          eqToHom
            (congrArg (mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L))
              (differentialGradedAlgebra_rightLeibniz_index n m))) := sorry

/-- The mapping-cone Leibniz law in the exact form required by the bundled module structure. -/
theorem mappingCone_d_smul_struct
    (f : K ⟶ L) (n m : ℤ) :
    mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n m ≫
        (mappingConeComplex (𝒜 := 𝒜) (K := K) (L := L) f).d (n + m) (n + m + 1) =
      ((mappingConeComplex (𝒜 := 𝒜) (K := K) (L := L) f).d n (n + 1) ▷
          𝒜.toComplex.X m) ≫
        mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) (n + 1) m ≫
        eqToHom
          (congrArg (mappingConeComplex (𝒜 := 𝒜) (K := K) (L := L) f).X
            (differentialGradedAlgebra_leftLeibniz_index n m)) +
      n.negOnePow •
        (((mappingConeComplex (𝒜 := 𝒜) (K := K) (L := L) f).X n ◁
            𝒜.toComplex.d m (m + 1)) ≫
          mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L) n (m + 1) ≫
          eqToHom
            (congrArg (mappingConeComplex (𝒜 := 𝒜) (K := K) (L := L) f).X
              (differentialGradedAlgebra_rightLeibniz_index n m))) := sorry

/-- Definition 24.22.2: the mapping cone of a differential graded `𝒜`-module morphism, with
degree-`n` term `L^n ⊞ K^(n + 1)` and the direct-sum `𝒜`-action. -/
@[stacks 0FS5]
noncomputable def mappingCone
    (f : K ⟶ L) : Mod(𝒜, d) where
  toComplex := mappingConeComplex (𝒜 := 𝒜) (K := K) (L := L) f
  smul := mappingConeSmul (𝒜 := 𝒜) (K := K) (L := L)
  smul_assoc := mappingCone_smul_assoc (𝒜 := 𝒜) (K := K) (L := L)
  one_smul := mappingCone_one_smul (𝒜 := 𝒜) (K := K) (L := L)
  d_smul := mappingCone_d_smul_struct (𝒜 := 𝒜) (K := K) (L := L) f

/-- The degree-`n` term of `mappingCone f` is `L^n ⊞ K^(n + 1)`. -/
@[simp]
theorem mappingCone_X (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).toComplex.X n = (L.toComplex.X n ⊞ K.toComplex.X (n + 1)) := sorry

/-- The degree-`n` evaluation of `mappingCone f`. -/
@[simp]
theorem mappingCone_apply (f : K ⟶ L) (n : ℤ) :
    mappingCone f n = (L n ⊞ K (n + 1)) := sorry

/-- The mapping-cone differential in the textbook biproduct ordering. -/
theorem mappingCone_d_desc_lift
    (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).toComplex.d n (n + 1) =
      biprod.desc
        (L.toComplex.d n (n + 1) ≫ biprod.inl)
        (biprod.lift
          (f.toCochainMap.f (n + 1))
          (-K.toComplex.d (n + 1) ((n + 1) + 1))) := sorry

/-- The differential on `mappingCone f` is the textbook matrix in the ordered biproduct
`L^n ⊞ K^(n + 1)`. -/
theorem mappingCone_d
    (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).toComplex.d n (n + 1) =
      Biprod.ofComponents
        (L.toComplex.d n (n + 1))
        0
        (f.toCochainMap.f (n + 1))
        (-K.toComplex.d (n + 1) ((n + 1) + 1)) := sorry

/-- The degree-`n` term of a differential graded mapping cone is canonically isomorphic to the
corresponding term of `CochainComplex.mappingCone`. -/
noncomputable def mappingConeXIsoCochainMappingCone
    (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).toComplex.X n ≅ (CochainComplex.mappingCone f.toCochainMap).X n :=
  (cochainMappingConeXIso (𝒜 := 𝒜) (K := K) (L := L) f n).symm

/-- The degreewise comparison from `mappingCone f` to `CochainComplex.mappingCone` commutes with
differentials. -/
theorem mappingConeXIsoCochainMappingCone_comm
    (f : K ⟶ L) (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (mappingConeXIsoCochainMappingCone f i).hom ≫
        (CochainComplex.mappingCone f.toCochainMap).d i j =
      (mappingCone f).toComplex.d i j ≫
        (mappingConeXIsoCochainMappingCone f j).hom := sorry

/-- The underlying complex of a differential graded mapping cone is canonically isomorphic to
`CochainComplex.mappingCone` of the underlying cochain map. -/
noncomputable def mappingConeToCochainMappingCone
    (f : K ⟶ L) :
    (mappingCone f).toComplex ≅ CochainComplex.mappingCone f.toCochainMap :=
  HomologicalComplex.Hom.isoOfComponents
    (mappingConeXIsoCochainMappingCone f)
    (mappingConeXIsoCochainMappingCone_comm f)

namespace MappingCone

/-- The source summand inclusion as a homogeneous map of degree `-1`.

Because `mappingCone f` is ordered as `L^n ⊞ K^(n + 1)`, this is the second
biproduct inclusion in every degree. -/
noncomputable def inl (f : K ⟶ L) :
    GradedHom 𝒜 K (mappingCone f) (-1) where
  hom := fun n ↦
    eqToHom
        (congrArg K.toComplex.X
          (neg_add_cancel_right n 1).symm) ≫
      (biprod.inr : K.toComplex.X ((n + (-1)) + 1) ⟶
        mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) (n + (-1)))
  comm := sorry

/-- The target summand inclusion as a homogeneous map of degree `0`.

The name distinguishes this homogeneous coordinate from the closed ordinary morphism
`MappingCone.inr` owned by the triangle layer. -/
noncomputable def inrGraded (f : K ⟶ L) :
    GradedHom 𝒜 L (mappingCone f) 0 where
  hom := fun n ↦
    (biprod.inl : L.toComplex.X n ⟶
      mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n) ≫
      eqToHom
        (congrArg (mappingCone f).toComplex.X (add_zero n).symm)
  comm := sorry

/-- The source-summand projection as a homogeneous map of degree `1`.

For the ordering `L^n ⊞ K^(n + 1)`, this is the second biproduct projection. -/
noncomputable def fst (f : K ⟶ L) :
    GradedHom 𝒜 (mappingCone f) K 1 where
  hom := fun _ ↦ biprod.snd
  comm := sorry

/-- The target-summand projection as a homogeneous map of degree `0`.

For the ordering `L^n ⊞ K^(n + 1)`, this is the first biproduct projection. -/
noncomputable def snd (f : K ⟶ L) :
    GradedHom 𝒜 (mappingCone f) L 0 where
  hom := fun n ↦
    biprod.fst ≫
      eqToHom (congrArg L.toComplex.X (add_zero n).symm)
  comm := sorry

/-- The degreewise component of the degree-`-1` source inclusion. -/
@[simp]
theorem inl_hom (f : K ⟶ L) (n : ℤ) :
    (inl f).hom n =
      eqToHom
          (congrArg K.toComplex.X
            (neg_add_cancel_right n 1).symm) ≫
        (biprod.inr : K.toComplex.X ((n + (-1)) + 1) ⟶
          mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) (n + (-1))) := sorry

/-- The degreewise component of the degree-zero target inclusion. -/
@[simp]
theorem inrGraded_hom (f : K ⟶ L) (n : ℤ) :
    (inrGraded f).hom n =
      (biprod.inl : L.toComplex.X n ⟶
        mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n) ≫
        eqToHom
          (congrArg (mappingCone f).toComplex.X (add_zero n).symm) := sorry

/-- The degreewise component of the degree-one source projection. -/
@[simp]
theorem fst_hom (f : K ⟶ L) (n : ℤ) :
    (fst f).hom n =
      (biprod.snd :
        mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n ⟶
          K.toComplex.X (n + 1)) := sorry

/-- The degreewise component of the degree-zero target projection. -/
@[simp]
theorem snd_hom (f : K ⟶ L) (n : ℤ) :
    (snd f).hom n =
      (biprod.fst :
        mappingConeTerm (𝒜 := 𝒜) (K := K) (L := L) n ⟶
          L.toComplex.X n) ≫
        eqToHom (congrArg L.toComplex.X (add_zero n).symm) := sorry

/-- The Hom differential of the degree-`-1` source inclusion is the original map followed
by the degree-zero target inclusion. -/
@[simp]
theorem d_inl (f : K ⟶ L) :
    gradedHomDifferential (-1) (inl f) =
      gradedHomComp (inrGraded f) (homToCompHom f).val := sorry

/-- The degree-zero target inclusion is closed for the Hom differential. -/
@[simp]
theorem d_inrGraded (f : K ⟶ L) :
    gradedHomDifferential 0 (inrGraded f) = 0 := sorry

/-- The degree-one source projection is closed for the Hom differential. -/
@[simp]
theorem d_fst (f : K ⟶ L) :
    gradedHomDifferential 1 (fst f) = 0 := sorry

/-- The Hom differential of the degree-zero target projection is minus the source
projection followed by the original map. -/
@[simp]
theorem d_snd (f : K ⟶ L) :
    gradedHomDifferential 0 (snd f) =
      -gradedHomComp (homToCompHom f).val (fst f) := sorry

/-- The degree-`-1` source inclusion followed by the degree-one source projection is the
homogeneous identity. -/
@[simp]
theorem inl_fst (f : K ⟶ L) :
    gradedHomComp (fst f) (inl f) = gradedHomId K := sorry

/-- The degree-`-1` source inclusion followed by the target projection is zero. -/
@[simp]
theorem inl_snd (f : K ⟶ L) :
    gradedHomComp (snd f) (inl f) = 0 := sorry

/-- The degree-zero target inclusion followed by the source projection is zero. -/
@[simp]
theorem inrGraded_fst (f : K ⟶ L) :
    gradedHomComp (fst f) (inrGraded f) = 0 := sorry

/-- The degree-zero target inclusion followed by the target projection is the homogeneous
identity. -/
@[simp]
theorem inrGraded_snd (f : K ⟶ L) :
    gradedHomComp (snd f) (inrGraded f) = gradedHomId L := sorry

/-- The two homogeneous summand coordinates decompose the identity of the mapping cone. -/
theorem id_decomp (f : K ⟶ L) :
    castHom (add_neg_cancel 1)
          (gradedHomComp (inl f) (fst f)) +
        castHom (zero_add 0)
          (gradedHomComp (inrGraded f) (snd f)) =
      gradedHomId (mappingCone f) := sorry

end MappingCone

end

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
