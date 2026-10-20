/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Topology
import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory hiding IsDiscrete

universe u

section

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] (s : S)

/- Remark 68.4.1 (1): an étale morphism of schemes is flat, and hence generalizations lift along
it. -/
@[stacks 03II] #check
  (AlgebraicGeometry.Etale.flatAndGeneralizingMap f : Flat f ∧ GeneralizingMap f)
#check (inferInstance : Flat f)
#check (Flat.generalizingMap f : GeneralizingMap f)

/- Remark 68.4.1 (2): an étale morphism is unramified, an unramified morphism is locally
quasi-finite, and hence fibres are discrete. -/
@[stacks 03II] #check
  (AlgebraicGeometry.Unramified.locallyQuasiFinite : Unramified f → LocallyQuasiFinite f)
#check (inferInstance : Unramified f)
#check (inferInstance : LocallyQuasiFinite f)
#check (f.isDiscrete_preimage_singleton s : IsDiscrete (f ⁻¹' {s}))

end

section

variable {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] [QuasiCompact f] (s : S)

/- Remark 68.4.1 (3): a quasi-compact étale morphism is quasi-finite, and in particular has
finite fibres. -/
@[stacks 03II] #check
  (AlgebraicGeometry.Scheme.Hom.instQuasiFinite f : AlgebraicGeometry.Scheme.Hom.QuasiFinite f)
#check
  (Scheme.Hom.QuasiFinite.finiteFibers f :
    Scheme.Hom.QuasiFinite f →
      ∀ t : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({t} : Set S)))
#check (f.finite_preimage_singleton s : (f ⁻¹' {s}).Finite)

end

section

variable {k : Type u} [Field k] (X : SchemeOverField k)

/- Remark 68.4.1 (4): an étale scheme over a field k is a disjoint union of spectra of finite
separable field extensions of k. -/
@[stacks 03II] #check
  (AlgebraicGeometry.etale_iff_schemeAsDisjointUnionOfSpecFiniteSeparable X :
    Etale X.hom ↔ Nonempty (SchemeAsDisjointUnionOfSpecFiniteSeparable k X))

end

-- See also Étale Morphisms, Section 41.11, for a general discussion of étale morphisms.
