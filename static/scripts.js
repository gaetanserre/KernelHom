window.addEventListener('load', function () {
  document.querySelectorAll('p').forEach(function (p) {
    if (p.querySelector('img')) {
      p.setAttribute('align', 'center');
    }
  });

  document.querySelectorAll('a[href]').forEach(function (link) {
    const url = new URL(link.href, window.location.href);
    if (url.hostname !== window.location.hostname) {
      link.setAttribute('target', '_blank');
      link.setAttribute('rel', 'noopener noreferrer');
    }
  });
});

window.addEventListener('load', () => {
  // 1. Add 'Try it!' and 'Copy' buttons to code blocks
  const blocks = document.querySelectorAll('code.hl.lean.block');
  blocks.forEach(block => {
    const code = block.innerText;

    // Create actions container
    const actions = document.createElement('div');
    actions.className = 'code-block-actions';
    block.addEventListener('scroll', () => {
      actions.style.transform = `translateX(${block.scrollLeft}px)`;
    });
    // Copy button
    const copyButton = document.createElement('button');
    copyButton.className = 'copy-button';
    copyButton.title = 'Copy to clipboard';
    const copyIcon = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" style="pointer-events: none;"><rect x="9" y="9" width="13" height="13" rx="2" ry="2"></rect><path d="M5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1"></path></svg>';
    const checkIcon = '<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><polyline points="20 6 9 17 4 12"></polyline></svg>';
    copyButton.innerHTML = copyIcon;

    copyButton.addEventListener('click', () => {
      navigator.clipboard.writeText(code).then(() => {
        copyButton.innerHTML = checkIcon;
        setTimeout(() => {
          copyButton.innerHTML = copyIcon;
        }, 2000);
      });
    });

    // Try it button
    const header = "import Mathlib\nopen MeasureTheory ProbabilityTheory CategoryTheory\n-- If any imports are missing from the default header, please manually add them.\n\n";
    const url = 'https://live.lean-lang.org/#code=' + encodeURIComponent(header + code);
    const tryItButton = document.createElement('a');
    tryItButton.href = url;
    tryItButton.target = '_blank';
    tryItButton.className = 'try-it-button';
    tryItButton.title = 'Open in Lean 4 Web Editor';
    tryItButton.innerHTML = `
      <svg width="12" height="12" viewBox="0 0 24 24"><path d="M8 5v14l11-7z"></path></svg>
      <span>Try it!</span>
    `;

    actions.appendChild(copyButton);
    // actions.appendChild(tryItButton);
    block.appendChild(actions);
  });
});

window.addEventListener('load', () => {
  const blocks = document.querySelectorAll('code.hl.lean.block');
  blocks.forEach(block => {
    colorizeParentheses(block);
  });
});
function colorizeParentheses(node) {
  const walker = document.createTreeWalker(
    node,
    NodeFilter.SHOW_TEXT,
    null,
    false
  );
  const nodesToReplace = [];
  let currentNode;
  while (currentNode = walker.nextNode()) {
    nodesToReplace.push(currentNode);
  }
  nodesToReplace.forEach(textNode => {
    const text = textNode.nodeValue;
    if (text && /[\(\)\[\]\{\}]/.test(text)) {
      const fragment = document.createDocumentFragment();
      let lastIndex = 0;
      const regex = /[\(\)\[\]\{\}]/g;
      let match;
      while ((match = regex.exec(text)) !== null) {
        if (match.index > lastIndex) {
          fragment.appendChild(
            document.createTextNode(text.substring(lastIndex, match.index))
          );
        }
        const span = document.createElement('span');
        span.className = 'separator';
        span.textContent = match[0];
        fragment.appendChild(span);
        lastIndex = match.index + 1;
      }
      if (lastIndex < text.length) {
        fragment.appendChild(
          document.createTextNode(text.substring(lastIndex))
        );
      }
      textNode.parentNode.replaceChild(fragment, textNode);
    }
  });
}