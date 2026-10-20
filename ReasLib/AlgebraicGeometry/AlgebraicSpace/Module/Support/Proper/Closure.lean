/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper.FiniteUnion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

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
    (hF : ProperOver f (closedSupport F)) (hG : ProperOver f (closedSupport G)) :
    ProperOver f (closedSupport (F ⊞ G)) :=
  sorry

/-- In a short exact sequence of modules, properness of the closed supports of the
outer finite-type quasi-coherent terms implies the same for the middle term. -/
theorem closedSupport_middle_of_shortExact_isProperOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (C : ShortComplex X.Modules) [C.X₁.IsFiniteType] [C.X₁.IsQuasicoherent]
    [C.X₃.IsFiniteType] [C.X₃.IsQuasicoherent]
    (h₁ : ProperOver f (closedSupport C.X₁)) (h₃ : ProperOver f (closedSupport C.X₃))
    (hC : C.ShortExact) :
    ProperOver f (closedSupport C.X₂) :=
  sorry

/-- The image of a morphism between finite-type quasi-coherent modules whose
closed supports are proper over a base remains proper over that base. -/
theorem closedSupport_image_isProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (F G : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] [G.IsFiniteType] [G.IsQuasicoherent]
    (hF : ProperOver f (closedSupport F)) (hG : ProperOver f (closedSupport G))
    (u : F ⟶ G) :
    ProperOver f (closedSupport (Abelian.image u)) :=
  sorry

/-- The cokernel of a morphism between finite-type quasi-coherent modules whose
closed supports are proper over a base remains proper over that base. -/
theorem closedSupport_cokernel_isProperOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (F G : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    [G.IsFiniteType] [G.IsQuasicoherent]
    (hF : ProperOver f (closedSupport F)) (hG : ProperOver f (closedSupport G))
    (u : F ⟶ G) :
    ProperOver f (closedSupport (cokernel u)) :=
  sorry

/-- A quasi-coherent quotient of a finite-type quasi-coherent module whose closed
support is proper over a base remains proper over that base. -/
theorem closedSupport_of_epi_isProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {F Q : X.Modules}
    [F.IsFiniteType] [F.IsQuasicoherent] [Q.IsQuasicoherent]
    (hF : ProperOver f (closedSupport F)) (q : F ⟶ Q) [Epi q] :
    ProperOver f (closedSupport Q) :=
  sorry

/-- On an algebraic space locally of finite type over a locally Noetherian base,
coherent modules whose closed support is proper over that base form a Serre class. -/
instance coherent_closedSupport_isProperOver_isSerreClass {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] :
    ObjectProperty.IsSerreClass
      ((fun ℱ : Coh X ↦ ProperOver f (closedSupport ℱ.obj)) :
        ObjectProperty (Coh X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
