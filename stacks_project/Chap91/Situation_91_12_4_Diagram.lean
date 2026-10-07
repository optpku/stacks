module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.Quotient
public import stacks_project.Chap91.Situation_91_12_2_Diagram

/-!
# Short exact sequences of flat first-order thickenings

After identifying underlying topoi, Situation 91.12.4 is a 3-column commutative
diagram of same-site first-order thickenings along `f : O_B ⟶ O`. The top and
bottom rows are short exact sequences of thickenings, each thickened map
restricts to `f`, each pair is strict, each thickened map is flat, and an
`O'_2`-module flat over `O_{B'_2}` extends to the `O`-module `F'_2 ⊗ O` along `π2`. The
canonical splitting of the top row is the same-site `canonicalTrivialization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules
open SheafOfModules.ChangeOfRings
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {O O1' O2' O3' : Sheaf J CommRingCat.{max u v}}
variable {π1 : O1' ⟶ O} {π2 : O2' ⟶ O} {π3 : O3' ⟶ O}
variable [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
variable [IsFirstOrderThickening π3]

/-- The kernel of `π3` is contained in the kernel of the composite `O'3 ⟶ O'1`
of a complex of first-order thickenings. -/
theorem isComplex_kernel_le (h : Hom π1 π2) (g : Hom π2 π3) (hC : IsComplex h g) :
    KernelIdeal.subobject π3 ≤ KernelIdeal.subobject (g.hom ≫ h.hom) := sorry

/-- The canonical splitting `O ⟶ O'1` of a complex of first-order thickenings,
obtained by eliminating `ker π3` and lifting the composite `O'3 ⟶ O'1`. -/
noncomputable def canonicalTrivialization (h : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex h g) : O ⟶ O1' :=
  (KernelIdeal.quotientIso π3 (KernelIdeal.quotientComparison_isIso π3)).inv ≫
    IdealSheaf.Quotient.lift (KernelIdeal.subobject π3) (g.hom ≫ h.hom)
      (isComplex_kernel_le h g hC)

/-- The canonical trivialization is a section of `π1`. -/
theorem canonicalTrivialization_isTrivialization (h : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex h g) :
    IsTrivialization (canonicalTrivialization h g hC) π1 := sorry

/-- The composite `O'3 ⟶ O'1` factors through `π3` as
`π3 ≫ canonicalTrivialization`. -/
theorem comp_eq_canonicalTrivialization_comp (h : Hom π1 π2) (g : Hom π2 π3)
    (hC : IsComplex h g) :
    g.hom ≫ h.hom = π3 ≫ canonicalTrivialization h g hC := sorry

/-- A 3-column commutative diagram of first-order thickenings along a same-site
morphism `f : O_B ⟶ O`, whose rows are short exact sequences of thickenings,
each thickened map restricts to `f`, each pair is strict, each thickened map is
flat, and an `O'_2`-module is flat over `O_{B'_2}`. -/
structure FlatMorphismShortExact
    {O O_B O1' O2' O3' OB1' OB2' OB3' : Sheaf J CommRingCat.{max u v}}
    (f : O_B ⟶ O) (π1 : O1' ⟶ O) (π2 : O2' ⟶ O) (π3 : O3' ⟶ O)
    (τ1 : OB1' ⟶ O_B) (τ2 : OB2' ⟶ O_B) (τ3 : OB3' ⟶ O_B)
    [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
    [IsFirstOrderThickening π3]
    [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
    [IsFirstOrderThickening τ3]
    [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
    [(restrictScalars (ringSheafMap π2)).IsRightAdjoint] where
  /-- The morphism `h` of first-order thickenings of `O`. -/
  h : Hom π1 π2
  /-- The morphism `g` of first-order thickenings of `O` from the third column. -/
  g : Hom π2 π3
  /-- The morphism of first-order thickenings of `O_B` from the first column. -/
  base : Hom τ1 τ2
  /-- The morphism of first-order thickenings of `O_B` from the third column. -/
  base' : Hom τ2 τ3
  /-- The thickened structure map `f'_1`. -/
  f1' : OB1' ⟶ O1'
  /-- The thickened structure map `f'_2`. -/
  f2' : OB2' ⟶ O2'
  /-- The thickened structure map `f'_3`. -/
  f3' : OB3' ⟶ O3'
  /-- The pair `(f, f'_1)` restricts to `f`. -/
  comm1 : f1' ≫ π1 = τ1 ≫ f
  /-- The pair `(f, f'_2)` restricts to `f`. -/
  comm2 : f2' ≫ π2 = τ2 ≫ f
  /-- The pair `(f, f'_3)` restricts to `f`. -/
  comm3 : f3' ≫ π3 = τ3 ≫ f
  /-- The left thickened ring-sheaf square commutes. -/
  comm_h : f2' ≫ h.hom = base.hom ≫ f1'
  /-- The right thickened ring-sheaf square commutes. -/
  comm_g : f3' ≫ g.hom = base'.hom ≫ f2'
  /-- The pair `(f, f'_1)` is a strict morphism of thickenings. -/
  strict1 : IsStrict f f1' comm1
  /-- The pair `(f, f'_2)` is a strict morphism of thickenings. -/
  strict2 : IsStrict f f2' comm2
  /-- The pair `(f, f'_3)` is a strict morphism of thickenings. -/
  strict3 : IsStrict f f3' comm3
  /-- The morphism `f'_1` is flat. -/
  flat1 : IsFlatHom f1'
  /-- The morphism `f'_2` is flat. -/
  flat2 : IsFlatHom f2'
  /-- The morphism `f'_3` is flat. -/
  flat3 : IsFlatHom f3'
  /-- The top row is a short exact sequence of first-order thickenings of `O`. -/
  ses_top : IsShortExact h g
  /-- The bottom row is a short exact sequence of first-order thickenings of `O_B`. -/
  ses_base : IsShortExact base base'
  /-- The `O'_2`-module `F'_2`. -/
  module : ringedSiteModuleCategory.{u, v, max u v, max u v} J O2'
  /-- The module `F'_2` is flat over `O_{B'_2}`. -/
  module_isFlatOver : IsFlat OB2' ((restrictionAlong f2').obj module)

namespace FlatMorphismShortExact

variable {O O_B O1' O2' O3' OB1' OB2' OB3' : Sheaf J CommRingCat.{max u v}}
variable {f : O_B ⟶ O} {π1 : O1' ⟶ O} {π2 : O2' ⟶ O} {π3 : O3' ⟶ O}
variable {τ1 : OB1' ⟶ O_B} {τ2 : OB2' ⟶ O_B} {τ3 : OB3' ⟶ O_B}
variable [IsFirstOrderThickening π1] [IsFirstOrderThickening π2]
variable [IsFirstOrderThickening π3]
variable [IsFirstOrderThickening τ1] [IsFirstOrderThickening τ2]
variable [IsFirstOrderThickening τ3]
variable [(restrictScalars (ringSheafMap f)).IsRightAdjoint]
variable [(restrictScalars (ringSheafMap π2)).IsRightAdjoint]

/-- Assemble a 3-column flat short exact diagram from its thickening morphisms,
structure maps, commutativities, strictness, flatness, short exactness, and the
stored middle module. -/
def of (h : Hom π1 π2) (g : Hom π2 π3) (base : Hom τ1 τ2) (base' : Hom τ2 τ3)
    (f1' : OB1' ⟶ O1') (f2' : OB2' ⟶ O2') (f3' : OB3' ⟶ O3')
    (comm1 : f1' ≫ π1 = τ1 ≫ f) (comm2 : f2' ≫ π2 = τ2 ≫ f)
    (comm3 : f3' ≫ π3 = τ3 ≫ f)
    (comm_h : f2' ≫ h.hom = base.hom ≫ f1')
    (comm_g : f3' ≫ g.hom = base'.hom ≫ f2')
    (strict1 : IsStrict f f1' comm1) (strict2 : IsStrict f f2' comm2)
    (strict3 : IsStrict f f3' comm3)
    (flat1 : IsFlatHom f1') (flat2 : IsFlatHom f2') (flat3 : IsFlatHom f3')
    (ses_top : IsShortExact h g) (ses_base : IsShortExact base base')
    (F : ringedSiteModuleCategory.{u, v, max u v, max u v} J O2')
    (module_isFlatOver : IsFlat OB2' ((restrictionAlong f2').obj F)) :
    FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3 where
  h := h
  g := g
  base := base
  base' := base'
  f1' := f1'
  f2' := f2'
  f3' := f3'
  comm1 := comm1
  comm2 := comm2
  comm3 := comm3
  comm_h := comm_h
  comm_g := comm_g
  strict1 := strict1
  strict2 := strict2
  strict3 := strict3
  flat1 := flat1
  flat2 := flat2
  flat3 := flat3
  ses_top := ses_top
  ses_base := ses_base
  module := F
  module_isFlatOver := module_isFlatOver

/-- The `O`-module `F = F'_2 ⊗ O` obtained by extending scalars along `π2`. -/
noncomputable def restrictModule
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J O :=
  (extendScalars (ringSheafMap π2)).obj S.module

/-- `restrictModule` is extension of scalars of the stored `O'_2`-module along `π2`. -/
theorem restrictModule_spec (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    restrictModule S = (extendScalars (ringSheafMap π2)).obj S.module := sorry

/-- The canonical splitting `π : O ⟶ O'1` of the top short exact sequence. -/
noncomputable def canonicalTrivialization
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) : O ⟶ O1' :=
  FirstOrderThickening.canonicalTrivialization S.h S.g
    (isShortExact_isComplex S.h S.g S.ses_top)

/-- The front restriction square of `(f, f'_1)`. -/
theorem frontSq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq S.f1' τ1 π1 f := sorry

/-- The middle restriction square of `(f, f'_2)`. -/
theorem middleSq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq S.f2' τ2 π2 f := sorry

/-- The back restriction square of `(f, f'_3)`. -/
theorem backSq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq S.f3' τ3 π3 f := sorry

/-- The left thickened ring-sheaf square. -/
theorem leftSq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq S.f2' S.base.hom S.h.hom S.f1' := sorry

/-- The right thickened ring-sheaf square. -/
theorem rightSq (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    CommSq S.f3' S.base'.hom S.g.hom S.f2' := sorry

/-- The pair `(f, f'_1)` is a strict morphism of thickenings. -/
theorem isStrict_fst (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsStrict f S.f1' S.comm1 := sorry

/-- The pair `(f, f'_2)` is a strict morphism of thickenings. -/
theorem isStrict_snd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsStrict f S.f2' S.comm2 := sorry

/-- The pair `(f, f'_3)` is a strict morphism of thickenings. -/
theorem isStrict_thd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsStrict f S.f3' S.comm3 := sorry

/-- The morphism `f'_1` is flat. -/
theorem isFlatHom_fst (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsFlatHom S.f1' := sorry

/-- The morphism `f'_2` is flat. -/
theorem isFlatHom_snd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsFlatHom S.f2' := sorry

/-- The morphism `f'_3` is flat. -/
theorem isFlatHom_thd (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    IsFlatHom S.f3' := sorry

/-- The comparison `(f'_1)^* J_1 ⟶ I_1` of kernel ideals. -/
noncomputable def idealMap_fst
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (extendScalars (ringSheafMap f)).obj (ideal τ1) ⟶ ideal π1 :=
  kernelPullbackMap f S.f1' S.comm1

/-- The comparison `(f'_2)^* J_2 ⟶ I_2` of kernel ideals. -/
noncomputable def idealMap_snd
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (extendScalars (ringSheafMap f)).obj (ideal τ2) ⟶ ideal π2 :=
  kernelPullbackMap f S.f2' S.comm2

/-- The comparison `(f'_3)^* J_3 ⟶ I_3` of kernel ideals. -/
noncomputable def idealMap_thd
    (S : FlatMorphismShortExact f π1 π2 π3 τ1 τ2 τ3) :
    (extendScalars (ringSheafMap f)).obj (ideal τ3) ⟶ ideal π3 :=
  kernelPullbackMap f S.f3' S.comm3

end FlatMorphismShortExact

end SheafOfModules.RingedSite.FirstOrderThickening
