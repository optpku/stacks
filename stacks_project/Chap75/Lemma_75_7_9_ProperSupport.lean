module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import stacks_project.Chap67.Lemma_67_23_5
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
public import stacks_project.Chap75.Lemma_75_7_8_ClosedSupport

/-!
# Proper support of modules under abelian operations

Finite-type quasi-coherent modules whose closed support is proper over a base
are closed under biproducts, extensions, images, cokernels, and quasi-coherent
quotients. Over a locally Noetherian base, coherent modules with this support
condition form a Serre class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace ClosedSubset Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The biproduct of two finite-type quasi-coherent modules whose closed supports
are proper over a base remains proper over that base. -/
theorem closedSupport_biprod_isProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (F G : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] [IsProperOver f (closedSupport G)] :
    IsProperOver f (closedSupport (F ⊞ G)) :=
  sorry

/-- Properness of closed support over a base is preserved by biproducts. -/
instance instIsProperOverClosedSupportBiprod {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F G : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [G.IsFiniteType] [G.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] [IsProperOver f (closedSupport G)] :
    IsProperOver f (closedSupport (F ⊞ G)) :=
  closedSupport_biprod_isProperOver f F G

/-- In a short exact sequence of modules, properness of the closed supports of the
outer finite-type quasi-coherent terms implies the same for the middle term. -/
theorem closedSupport_middle_of_shortExact_isProperOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (C : ShortComplex X.Modules) [C.X₁.IsFiniteType] [C.X₁.IsQuasicoherent]
    [C.X₃.IsFiniteType] [C.X₃.IsQuasicoherent]
    [IsProperOver f (closedSupport C.X₁)] [IsProperOver f (closedSupport C.X₃)]
    (hC : C.ShortExact) :
    IsProperOver f (closedSupport C.X₂) :=
  sorry

/-- The image of a morphism between finite-type quasi-coherent modules whose
closed supports are proper over a base remains proper over that base. -/
theorem closedSupport_image_isProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (F G : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] [IsProperOver f (closedSupport G)]
    (u : F ⟶ G) :
    IsProperOver f (closedSupport (Abelian.image u)) :=
  sorry

/-- Properness of closed support over a base is preserved by images. -/
instance instIsProperOverClosedSupportImage {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F G : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [G.IsFiniteType] [G.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] [IsProperOver f (closedSupport G)]
    (u : F ⟶ G) :
    IsProperOver f (closedSupport (Abelian.image u)) :=
  closedSupport_image_isProperOver f F G u

/-- The cokernel of a morphism between finite-type quasi-coherent modules whose
closed supports are proper over a base remains proper over that base. -/
theorem closedSupport_cokernel_isProperOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F G : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [G.IsFiniteType] [G.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] [IsProperOver f (closedSupport G)]
    (u : F ⟶ G) :
    IsProperOver f (closedSupport (cokernel u)) :=
  sorry

/-- Properness of closed support over a base is preserved by cokernels. -/
instance instIsProperOverClosedSupportCokernel {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F G : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [G.IsFiniteType] [G.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] [IsProperOver f (closedSupport G)]
    (u : F ⟶ G) :
    IsProperOver f (closedSupport (cokernel u)) :=
  closedSupport_cokernel_isProperOver f F G u

/-- A quasi-coherent quotient of a finite-type quasi-coherent module whose closed
support is proper over a base remains proper over that base. -/
theorem closedSupport_of_epi_isProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {F Q : X.Modules}
    [F.IsFiniteType] [F.IsQuasicoherent] [Q.IsQuasicoherent]
    [IsProperOver f (closedSupport F)] (q : F ⟶ Q) [Epi q] :
    IsProperOver f (closedSupport Q) :=
  sorry

/-- On an algebraic space locally of finite type over a locally Noetherian base,
coherent modules whose closed support is proper over that base form a Serre class. -/
instance coherent_closedSupport_isProperOver_isSerreClass {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] :
    ObjectProperty.IsSerreClass
      ((fun ℱ : Coh X ↦ IsProperOver f (closedSupport ℱ.obj)) :
        ObjectProperty (Coh X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
