/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surgery ledger

Aggregator for the `D3-surgery-ledger` task.  The module tree is:

* `Poincare.Longrun.Surgery.Basic` — surgery datum, ledger predicates, preservation
  obligations, and the homeomorphism / homotopy-equivalence certificates.
* `Poincare.Longrun.Surgery.Chain` — finite chains of surgery steps and the composition of
  preservation obligations.
* `Poincare.Longrun.Surgery.Toy` — a toy surgery relation with checked algebraic consequences.
* `Poincare.Longrun.Surgery.Missing` — the explicit separation of the missing geometric neck
  analysis and extinction theorem.
-/

import Poincare.Longrun.Surgery.Basic
import Poincare.Longrun.Surgery.Chain
import Poincare.Longrun.Surgery.Toy
import Poincare.Longrun.Surgery.Missing
