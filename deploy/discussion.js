const discussion = document.querySelector('#wechat-discussion');
const coreTeam = document.querySelector('#core-team');
function followCoreTeamLink() {
  if (coreTeam && location.hash === '#core-team') coreTeam.open = true;
}
followCoreTeamLink();
window.addEventListener('hashchange', followCoreTeamLink);
if (discussion) {
  const roomy = window.matchMedia('(min-width: 1200px) and (min-height: 650px)');
  const setting = 'goldbach-discussion-open';
  function fitDiscussion() {
    if (coreTeam?.open) return;
    let preference = null;
    try { preference = sessionStorage.getItem(setting); } catch {}
    discussion.open = preference === null ? roomy.matches : preference === 'yes';
  }
  fitDiscussion();
  roomy.addEventListener('change', fitDiscussion);
  discussion.querySelector('summary').addEventListener('click', () => {
    try { sessionStorage.setItem(setting, discussion.open ? 'no' : 'yes'); } catch {}
  });
}
