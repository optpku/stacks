/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.GeometricPoint
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry Scheme

universe u

@[expose] public section

noncomputable section

variable [∀ X : Scheme.{u}, HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable {S : Scheme.{u}} (s t : GeometricPoint S)
variable (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
variable (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
variable (F : Sheaf S.smallEtaleTopology (Type (u + 1)))

/- Remark 59.75.1 (Alternative description of sp) (1): genuine inverse-image
sections on the pointed strict henselization are identified with the stalk at `s`
by the canonical closed-point germ transformation. -/
@[stacks 0GJ3] #check (AlgebraicGeometry.Scheme.strictHenselianGlobalToStalk_isIso
  (Type (u + 1)) s : IsIso (strictHenselianGlobalToStalk (Type (u + 1)) s))

/- Remark 59.75.1 (Alternative description of sp) (2): germs identify sections
of the twice-pulled-back sheaf at the geometric lift with the original stalk at `t`. -/
@[stacks 0GJ3] #check (AlgebraicGeometry.Scheme.geometricPullbackSectionsToStalk_bijective
  s t point point_over F :
  Function.Bijective (geometricPullbackSectionsToStalk s t point point_over F))

/- Remark 59.75.1 (Alternative description of sp) (3): independently constructed
stalk specialization is pullback of sections along the geometric lift, under the
two canonical identifications. -/
@[stacks 0GJ3] #check (AlgebraicGeometry.Scheme.etaleSpecialization_eq_geometricPullback
  s t point point_over F :
  (strictHenselianGlobalToStalk (Type (u + 1)) s).app F ≫
      ((StrictHenselianNeighborhood.canonical s).specializationPoint
        point point_over).sheafFiber.app F =
    TypeCat.ofHom (etaleSectionsPullback point
      ((Sheaf.smallEtaleInverseImage (StrictHenselization.toScheme S s)
        (Type (u + 1))).obj F)) ≫
      TypeCat.ofHom (geometricPullbackSectionsToStalk s t point point_over F))

end
