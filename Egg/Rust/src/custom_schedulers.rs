use egg::*;
use log::*;


#[derive(Debug)]


pub struct PriorityScheduler {
    default_match_limit: usize,
    default_ban_length: usize,
    stats: IndexMap<Symbol, PriorityRuleStats>,
    map: IndexMap<usize, usize>
}


/// A [`RewriteScheduler`] that implements priority scheduling.
/// 
/// 
#[derive(Debug)]
struct PriorityRuleStats {
    times_applied: usize,
    banned_until: usize,
    times_banned: usize,
    match_limit: usize,
    ban_length: usize,
    priority: usize,
    latest_applied: IndexMap<usize, usize>,
    total_runs: usize
}

impl PriorityScheduler {
    pub fn with_priorities(mut self, map: IndexMap<usize, usize>) -> Self {
        self.map = map.clone();
        self
    }
}


impl<L, N> RewriteScheduler<L, N> for PriorityScheduler
where
    L: Language,
    N: Analysis<L>,
{

}

