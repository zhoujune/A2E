#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrashSite {
    AfterAuthorize,
    AfterPrepare,
    AfterArm,
    AfterStart,
    AfterInvoke,
    AfterOutcome,
    AfterTerminal,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CrashPlan {
    site: CrashSite,
    occurrence: u64,
    seen: u64,
    fired: bool,
}

impl CrashPlan {
    #[must_use]
    pub const fn once(site: CrashSite) -> Self {
        Self::on_occurrence(site, 1)
    }

    #[must_use]
    pub const fn on_occurrence(site: CrashSite, occurrence: u64) -> Self {
        Self {
            site,
            occurrence,
            seen: 0,
            fired: false,
        }
    }

    pub(crate) fn hit(&mut self, site: CrashSite) -> bool {
        if self.fired || self.site != site {
            return false;
        }
        self.seen = self.seen.saturating_add(1);
        if self.seen == self.occurrence {
            self.fired = true;
            true
        } else {
            false
        }
    }
}
