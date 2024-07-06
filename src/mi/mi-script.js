var _ = {
  easeScroll: function (x, y, duration, callback) {
    const startX = window.scrollX;
    const startY = window.scrollY;
    const distanceX = _.computeDistanceX(x);
    const distanceY = _.computeDistanceY(y);
    _.easeTween(duration, function (t) {
        window.scroll(
          t * distanceX + startX,
          t * distanceY + startY);
      },
      callback);
  },

  easeScrollX: function (x, duration, callback) {
    const startX = window.scrollX;
    const distanceX = _.computeDistanceX(x);
    _.easeTween(duration, function (t) {
        window.scroll(
          t * distanceX + startX,
          window.scrollY);
      },
      callback);
  },

  easeScrollY: function (y, duration, callback) {
    const startY = window.scrollY;
    const distanceY = _.computeDistanceY(y);
    _.easeTween(duration, function (t) {
        window.scroll(
          window.scrollX,
          t * distanceY + startY);
      },
      callback);
  },

  easeScrollElement: function (element, x, y, duration, callback) {
    const startX = element.scrollLeft;
    const startY = element.scrollTop;
    const distanceX = _.computeElementDistanceX(element, x);
    const distanceY = _.computeElementDistanceY(element, y);
    _.easeTween(duration, function (t) {
        element.scrollLeft = t * distanceX + startX;
        element.scrollTop = t * distanceY + startY;
      },
      callback);
  },

  easeScrollElementX: function (element, x, duration, callback) {
    const startX = element.scrollLeft;
    const distanceX = _.computeElementDistanceX(element, x);
    _.easeTween(duration, function (t) {
        element.scrollLeft = t * distanceX + startX;
      },
      callback);
  },

  easeScrollElementY: function (element, y, duration, callback) {
    const startY = element.scrollTop;
    const distanceY = _.computeElementDistanceY(element, y);
    _.easeTween(duration, function (t) {
        element.scrollTop = t * distanceY + startY;
      },
      callback);
  },

  computeDistanceX: function (x) {
    return (
      _.computeGenericDistance(x,
        document.body.scrollWidth,
        window.innerWidth,
        window.scrollX));
  },

  computeDistanceY: function (y) {
    return (
      _.computeGenericDistance(y,
        document.body.scrollHeight,
        window.innerHeight,
        window.scrollY));
  },

  computeElementDistanceX: function (element, x) {
    return (
      _.computeGenericDistance(x,
        element.scrollWidth,
        element.clientWidth,
        element.scrollLeft));
  },

  computeElementDistanceY: function (element, y) {
    return (
      _.computeGenericDistance(y,
        element.scrollHeight,
        element.clientHeight,
        element.scrollTop));
  },

  computeGenericDistance: function (z, scrollSize, clientSize, startZ) {
    return (
      Math.max(0,
        Math.min(z,
          scrollSize - clientSize)) - startZ);
  },

  easeTween: function (duration, step, callback) {
    _.tween(duration, function (t) {
        return step(_.ease(t));
      },
      callback);
  },

  tween: function (duration, step, callback) {
    const start = Date.now();
    const end = start + duration;
    function loop() {
      const now = Date.now();
      if (now < end) {
        step((now - start) / duration);
        window.requestAnimationFrame(loop);
      } else if (callback) {
        callback();
      }
    }
    window.requestAnimationFrame(loop);
  },

  ease: function (t) {
    return (
      t <= 0 ? 0 :
      t >= 1 ? 1 :
      1.0042954579734844 * Math.exp(
        -6.4041738958415664 * Math.exp(
          -7.2908241330981340 * t)));
  }
};
