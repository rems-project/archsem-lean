-- SPDX-FileCopyrightText: 2026 Christopher Lang
--
-- SPDX-License-Identifier: Apache-2.0 OR BSD-2-Clause

import Std.Data.HashSet

namespace ArchSem.CandidateExecutions

abbrev Rel (α : Type) [Hashable α] [BEq α] := Std.HashSet (α × α)

end ArchSem.CandidateExecutions
