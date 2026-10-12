/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Central.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {k : Type u} {A : Type v} [CommRing k] [Ring A] [Algebra k A]

/-
Domain triage:
- primary domain: central algebras and centers.
- `source-facing`: the textbook notion that a `k`-algebra `A` is central.
- `core/canonical`: `Algebra.IsCentral k A`.
- `bridge/view`: `Algebra.IsCentral.mem_center_iff`.
- Primitive data vs derived API: the owner class `Algebra.IsCentral k A` is the primitive
  notion; the pointwise center characterization is derived API.
-/

/- Definition 11.2.4: a `k`-algebra `A` is central when its center is exactly the image of the
structure map `k → A`; this is the canonical mathlib class `Algebra.IsCentral k A`. -/
@[stacks 0742]
#check Algebra.IsCentral k A

/- Companion recall: for a central `k`-algebra, an element lies in the center exactly when it lies
in the image of the structure map `k → A`. -/
recall Algebra.IsCentral.mem_center_iff
